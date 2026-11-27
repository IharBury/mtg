import Mtg.Engine.Game.Costs

/-!
# Casting legality and payment (CR 601)

Cast timing (flash, sorcery speed), castability from each zone,
restrictions on proposed spells, choosing mana sources for a proposal,
paying costs, reversing an illegal proposal (CR 734.1), ward
(CR 702.21), locking in targets, and becoming cast or activated.
-/

namespace Mtg.Engine
namespace Game

/-- Captain Mar-Vell: as though spells had flash while an opponent has
cast a spell this turn (MSH 105). The permanent need not have been on
the battlefield when that spell was cast. -/
def cosmicAwarenessFlash (g : Game) (p : PlayerId) : Bool :=
  g.battlefield.any fun o =>
    let env : EvalEnv := { controller := (g.controllerOf o).getD o.owner, sourceId := some o.id }
    (g.staticAbilities o).any fun ab =>
      ab.anyRule fun cond? r =>
        match r with
        | .play (.castAsThoughFlash who .anyObject false none) =>
          EvalExpr.matchesPlayerFilter g env who p && cond?.all (EvalExpr.evalCondition g env)
        | _ => false

/-- Timing check shared by beginning to cast a spell or an Adventure (CR 601.3)
and CR 601.2b Morph vs. printed-face selection (`excludeStackId := some prop.spellId`). -/
def timingAllowsCast (g : Game) (p : PlayerId) (face : CardDef)
    (excludeStackId : Option ObjectId := none)
    (ignorePending : Bool := false)
    (card? : Option GameObject := none) : Bool :=
  let dummy : GameObject :=
    card?.getD
      { id := noSourceSentinelId, owner := p, controller := some p, zone := .hand p,
        printed := face, status := if face.name == "" then { faceDown := true } else {} }
  let spellObj : GameObject :=
    { dummy with
      zone := .stack
      controller := some p
      printed := face
      status := { dummy.status with faceDown := (face.name == "") } }
  let faceStatics := g.staticAbilities spellObj
  let selfEnv : EvalEnv := { controller := p, sourceId := card?.map (·.id) }
  let hasSelfFlash :=
    faceStatics.any fun ab =>
      ab.anyRule fun cond? r =>
        match r with
        | .play (.castAsThoughFlash who spellPred true nth?) =>
          EvalExpr.matchesPlayerFilter g selfEnv who p &&
            cond?.all (EvalExpr.evalCondition g selfEnv) &&
            nth?.all (fun n => g.countMatchingSpellsCastThisTurn p selfEnv spellPred + 1 == n)
        | _ => false
  let spellView := EvalExpr.spellFaceView g dummy face p (g.actualCastManaValue dummy face)
  let hasPeerFlash :=
    g.battlefield.any fun o =>
      let env : EvalEnv := { controller := (g.controllerOf o).getD o.owner, sourceId := some o.id }
      (g.staticAbilities o).any fun ab =>
        ab.anyRule fun cond? r =>
          match r with
          | .play (.castAsThoughFlash who spellPred false nth?) =>
            EvalExpr.matchesPlayerFilter g env who p &&
              cond?.all (EvalExpr.evalCondition g env) &&
              EvalExpr.evalObjectPred g env spellView spellPred &&
              nth?.all (fun n => g.countMatchingSpellsCastThisTurn p env spellPred + 1 == n)
          | _ => false
  let prioOk :=
    if excludeStackId.isSome || ignorePending then
      !g.over && g.priority == p && g.playersReceivePriority
    else g.hasPriority p
  let sorceryOk :=
    match excludeStackId with
    | some sid =>
      !g.over && !(g.stack.any (·.objectId != sid)) &&
        g.step.isMainPhase && g.activePlayer == p && g.priority == p
    | none =>
      if ignorePending then
        !g.over && g.stack.isEmpty &&
          g.step.isMainPhase && g.activePlayer == p && g.priority == p
      else g.asSorcery? p
  let (faceTypes, _, _) := g.faceCdaCharacteristics spellObj face
  let faceHasSorcerySpeed :=
    !faceTypes.contains .instant && !faceTypes.contains .land &&
      !KeywordAbility.hasFlash (g.currentKeywords spellObj)
  prioOk &&
  (if faceHasSorcerySpeed && !hasSelfFlash && !hasPeerFlash then
    sorceryOk else true)

/-- Every card face the game knows: each object's card, its other face,
Adventure (CR 716), and prepare spell (CR 723), and each sideboard card.
Alternative names of adventurer and preparation cards are judged by their
alternative characteristics (CR 201.4f; ruling 745). -/
def knownCardFaces (g : Game) : Array CardDef :=
  let faces (c : CardDef) : Array CardDef :=
    #[c] ++ c.otherFace.toArray ++ (c.adventure.map (·.toCardDef)).toArray ++
      (c.prepareFace.map (·.toCardDef)).toArray
  let fromObjects := g.objects.foldl (fun acc o => acc ++ faces o.printed) #[]
  g.players.foldl (fun acc pl => pl.sideboard.foldl (fun acc c => acc ++ faces c) acc) fromObjects

/-- Whether `name` is the name of a nonland card (CR 201.4a, 201.4f). -/
def isNonlandCardName (g : Game) (name : String) : Bool :=
  g.knownCardFaces.any (fun c => c.name == name && !c.isLand)

/-- Whether a permanent forbids casting spells named `name` (Meddling Mage, CR 601.2 / 101.2). -/
def spellNameForbidden (g : Game) (name : String) : Bool :=
  g.battlefield.any (fun o =>
    o.status.chosenName == some name &&
      let env : EvalEnv := { controller := (g.controllerOf o).getD o.owner, sourceId := some o.id }
      (g.staticAbilities o).any fun ab =>
        ab.anyRule fun cond? r =>
          match r with
          | .player (.cantCastSpells _ (.named .chosenOnSource)) =>
            cond?.all (EvalExpr.evalCondition g env)
          | _ => false)

/-- Whether any living member of the active team controls a permanent forbidding
opponents from casting spells during that player's turn (CR 101.2 / 805.4a / 810.2). -/
def opponentsCantCastOnActiveTurn (g : Game) (p : PlayerId) : Bool :=
  g.battlefield.any fun o =>
    let srcCtrl := (g.controllerOf o).getD o.owner
    g.stillInGame srcCtrl &&
      let env : EvalEnv := { controller := srcCtrl, sourceId := some o.id }
      (g.staticAbilities o).any fun ab =>
        ab.anyRule fun cond? r =>
          match r with
          | .player (.cantCastSpells who .anyObject) =>
            cond?.all (EvalExpr.evalCondition g env) &&
              EvalExpr.matchesPlayerFilter g env who p
          | _ => false

/-- Minimum number of other cards in graveyard required by a `castRestriction` static on `face`,
if any (Ruling 852). -/
def castOnlyIfGraveyardAtLeast? (face : CardDef) : Option Nat :=
  face.staticAbilities.findSome? fun ab =>
    match ab with
    | .ruleModifying _ (.play (.castRestriction
        (.cmp .ge (.aggregate .count .one (.inZones .yourGraveyard (.otherThan .this))) (.const n)))) =>
      some n.toNat
    | _ => none

/-- Whether every `StaticPlayRule.castRestriction` on `face` is satisfied for `p` casting `cardId`
(CR 601.2 / 101.2; Ruling 852). -/
def graveyardCastThresholdMet (g : Game) (p : PlayerId) (cardId : ObjectId) (face : CardDef) : Bool :=
  let faceStatics :=
    match g.findObject? cardId with
    | some o =>
      g.staticAbilities
        { o with
          zone := .stack
          controller := some p
          printed := face
          status := { o.status with faceDown := (face.name == "") } }
    | none => face.staticAbilities
  let env : EvalEnv := { controller := p, sourceId := some cardId }
  faceStatics.all fun ab =>
    match ab with
    | .ruleModifying cond? (.play (.castRestriction unlessCond)) =>
      if cond?.all (EvalExpr.evalCondition g env) then
        EvalExpr.evalCondition g env unlessCond
      else true
    | _ => true

/-- Error message when `face`'s `castRestriction` prevents `p` from casting `cardId`. -/
def castRestrictionError? (g : Game) (p : PlayerId) (cardId : ObjectId) (face : CardDef) :
    Option String :=
  if g.graveyardCastThresholdMet p cardId face then none
  else
    match castOnlyIfGraveyardAtLeast? face with
    | some n => some s!"{face.name} can be cast only with {n} or more other cards in your graveyard"
    | none => some s!"{face.name} can't be cast right now"

/-- Why a mandatory sacrifice additional cost of `face` cannot be paid, if it cannot
(CR 601.2b / 601.2h / 601.3). -/
def mandatorySacrificeError? (g : Game) (p : PlayerId) (checkId : ObjectId)
    (face : CardDef) (displayName : String := face.name)
    (excludeExtra? : Option ObjectId := none) : Option String :=
  match g.mandatorySacrificeFilterForId? checkId face with
  | none => none
  | some pred =>
    let env : EvalEnv := { controller := p, sourceId := some checkId }
    if (g.permanentsOf p).any (fun perm =>
        perm.id != checkId && excludeExtra? != some perm.id &&
          EvalExpr.evalObjectPred g env (.live perm) pred) then
      none
    else
      let phrase := (CostSpec.ofItem (.sacrifice (.exact 1) (.filter pred))).toInlinePhrase
      let target := if phrase.startsWith "sacrifice " then (phrase.drop 10).copy else phrase
      some s!"{displayName} requires sacrificing {target}"

/-- Whether card face `c` has a legal target to begin casting it: enough unkicked
targets (or an Aura target when `c.spellEffect = none`), or — when `c` has a
target-replacing kicker that may be chosen — enough kicked targets
(CR 115.1 / 601.2b–c / 702.33d,g). -/
def castFaceHasLegalTarget (g : Game) (p : PlayerId) (c : CardDef)
    (tcs : Array TextChange := #[]) (sourceId : Option ObjectId := none) : Bool :=
  let unkickedOk :=
    if isModalSpellFace c then
      (effectiveSpellModes c).any (fun e =>
        let m := if tcs.isEmpty then e else TextChange.applyEffect tcs e
        g.spellModeIsChoosable p m sourceId) ||
        isReturnUpToTwoGyModal c || c.allowsZeroTargets
    else
      match c.spellEffect with
      | some e =>
        let e' := if tcs.isEmpty then e else TextChange.applyEffect tcs e
        !e'.requiresTarget || e'.allowsZeroTargets || g.effectHasEnoughTargets p e' sourceId
      | none =>
        if c.isAura then c.allowsZeroTargets || !(g.legalAuraTargets p c sourceId).isEmpty
        else !(g.legalTargetsForFace p c none tcs sourceId).isEmpty
  unkickedOk || g.kickedFaceHasLegalTarget p c tcs sourceId

/-- Characteristics of a face-down Morph spell on the stack (CR 702.37a / 708.2a). -/
def morphSpellFace : CardDef :=
  { name := "", types := #[.creature], power := some (.fixed 2), toughness := some (.fixed 2),
    manaCost := ManaCost.ofGeneric 3 }

/-- Whether `p` may begin to cast `o` face down via Morph (CR 702.37a,c / 708.2). -/
def canCastMorphFaceDown (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  let kwFace := { g.baseCard o with keywords := g.currentKeywords o }
  let fromGraveyard := o.zone == .graveyard o.owner
  let perms := g.playPermissionsFor p o
  let cleanPerms :=
    perms.filter fun pm =>
      !pm.withoutManaCost && !pm.payLifeEqualManaValue && pm.prepareSource.isNone
  kwFace.morph.isSome && !fromGraveyard &&
    !g.splitSecondOnStack && !g.combatLocksNonManaAbilities &&
    !g.opponentsCantCastOnActiveTurn p && !g.spellNameForbidden "" &&
    !g.cantCastSpellsThisTurn p &&
    g.mayPlay p o &&
    (if perms.isEmpty then
      g.timingAllowsCast p morphSpellFace
     else
      cleanPerms.any (fun pm => pm.ignoreTiming || g.timingAllowsCast p morphSpellFace) ||
        (g.mayCastExiledBySource p o && g.timingAllowsCast p morphSpellFace))

/-- Whether `p` may begin to cast `o` using its front-face characteristics (CR 601.3). -/
def canCastFrontFace (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  let rawFace := g.baseCard o
  let kwFace := { rawFace with keywords := g.currentKeywords o }
  let fromGraveyard := o.zone == .graveyard o.owner
  let hadFlashbackPerm := fromGraveyard && g.flashbackUntilEot o
  let isFlashbackCast := fromGraveyard && (kwFace.flashback.isSome || hadFlashbackPerm)
  let perms := g.playPermissionsFor p o
  !g.isLand o && !g.splitSecondOnStack && !g.combatLocksNonManaAbilities &&
  !g.opponentsCantCastOnActiveTurn p && !g.spellNameForbidden (g.name o) &&
  !g.cantCastSpellsThisTurn p &&
  (o.zone != .library p || g.isCreature o) &&
  g.mayPlay p o &&
  g.graveyardCastThresholdMet p o.id rawFace &&
  (if perms.isEmpty then
    g.timingAllowsCast p rawFace (card? := some o)
   else
    perms.any (fun perm =>
      (perm.ignoreTiming || g.timingAllowsCast p rawFace (card? := some o)) &&
        (!perm.payLifeEqualManaValue || g.canPayLife p (g.objectManaValue o))) ||
      (g.mayCastExiledBySource p o && g.timingAllowsCast p rawFace (card? := some o))) &&
  (g.mandatorySacrificeError? p o.id rawFace).isNone &&
  (!(isFlashbackCast && kwFace.flashbackDiscard) || (g.discardableHandIds p).any (· != o.id)) &&
  -- Untargeted permanents, and untargeted instants/sorceries with a modeled
  -- effect (e.g. Night's Whisper), may be proposed (CR 601.3).
  if isModalSpellFace rawFace then
    let tcs := g.evalLayer3 o
    (effectiveSpellModes rawFace).any (fun e =>
      let m := if tcs.isEmpty then e else TextChange.applyEffect tcs e
      g.spellModeIsChoosable p m (some o.id)) ||
      isReturnUpToTwoGyModal rawFace || rawFace.allowsZeroTargets
  else if rawFace.requiresTarget then
    -- CR 601.2b–c / 702.33d,g: a target-replacing kicker may be chosen, so legal kicked
    -- targets (Galadriel's Dismissal's player) suffice when no unkicked target is legal.
    rawFace.allowsZeroTargets || g.castFaceHasLegalTarget p rawFace (g.evalLayer3 o) (some o.id)
  else rawFace.isPermanentCard || rawFace.spellEffect.isSome || isModalSpellFace rawFace

/-- Whether `p` may begin to cast `o` (CR 601.3 / 702.37a). Having enough mana
in the pool is not required; mana abilities are activated at CR 601.2g. Additional
non-mana costs such as sacrificing a permanent must still be payable. -/
def canCast (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  g.canCastFrontFace p o || g.canCastMorphFaceDown p o

/-- Whether `p` can pay a mandatory additional cost of `o` from `available`
(another card to discard, a permanent to sacrifice, or the generic
alternative). Mana abilities are not activated here. -/
def canPayAnnouncedAdditional (g : Game) (p : PlayerId) (o : GameObject)
    (available : ManaPool) (origPerm : Option PlayPermission := none)
    (explicitAltCost : Bool := false) (flashback : Option Bool := none)
    (useImplicitPermissions : Bool := true) : Bool :=
  let bc := g.baseCard o
  -- CR 106.6: pure `ManaSpend` for this spell — Elf, instant/sorcery, Hero,
  -- Villain, and artifact-spell mana may pay; creature-source mana pays only
  -- activated abilities, never a spell (MSH 75).
  let spend : ManaSpend :=
    { spell := true, fromHand := o.zone == .hand p
      castFromZone := some o.zone.kind
      supertypes := g.supertypes o, types := g.types o, subtypes := g.subtypes o }
  let canPay (cost : ManaCost) : Bool :=
    available.canPay cost spend
  match g.additionalChoiceCostFor? o bc with
  | none => true
  | some branches =>
    let env : EvalEnv := { controller := p, sourceId := some o.id }
    branches.any fun branch =>
      branch.items.all fun item =>
        match item with
        | .mana m =>
          canPay (g.playManaCost { o with controller := some p } bc m
            (origPerm := origPerm) (flashback := flashback) (explicitAltCost := explicitAltCost)
            (useImplicitPermissions := useImplicitPermissions))
        | .behold quality =>
          (g.permanentsOf p).any (fun perm => g.hasSubtype perm quality) ||
            (g.player p).hand.any (fun id =>
              id != o.id && (g.findObject? id).any (fun card => isDiscardableCard card && g.hasSubtype card quality))
        | .sacrifice _ (.filter pred) =>
          (g.permanentsOf p).any (fun perm =>
            perm.id != o.id && EvalExpr.evalObjectPred g env (.live perm) pred)
        | .discard _ .hand =>
          (g.discardableHandIds p).any (fun id => id != o.id)
        | .discard _ (.matching pred) =>
          (g.discardableHandIds p).any (fun id =>
            id != o.id && (g.findObject? id).any (fun c => EvalExpr.evalObjectPred g env (.live c) pred))
        | _ => true

/-- Whether `p` can pay `cost` for spell `spellObj` from their current mana pool
plus plain tap mana sources (including multi-color `ManaOutput.combination`
choices), excluding `excludeIds` (CR 106.1,6 / 601.2g). -/
def canPaySpellCostFromSources (g : Game) (p : PlayerId) (spellObj : GameObject)
    (cost : ManaCost) (fromHand : Bool := spellObj.zone == .hand p)
    (excludeIds : Array ObjectId := #[])
    (prop? : Option ProposedSpell := none)
    (castFromZone : Option ZoneKind := none) : Bool :=
  let originZone : ZoneKind :=
    castFromZone.getD (match prop? with | some pr => pr.original.zone.kind | none => spellObj.zone.kind)
  let spend : ManaSpend :=
    { spell := true, fromHand := fromHand
      castFromZone := some originZone
      supertypes := g.supertypes spellObj
      types := g.types spellObj
      subtypes := g.subtypes spellObj }
  let sources :=
    ((g.manaSources p).filter (fun (src, _) => !excludeIds.contains src.id)).toList
  g.canPayFromSources (g.player p).manaPool cost sources spend (prop? := prop?)

/-- Multi-choice `canPayFromSources` counterpart of `canPayAnnouncedAdditional`:
whether `p` can satisfy `o`'s mandatory behold/sacrifice/discard-or-pay-generic
additional cost (CR 118.8 / 601.2b,g). -/
def canPayAnnouncedAdditionalFromSources (g : Game) (p : PlayerId) (o : GameObject)
    (origPerm : Option PlayPermission := none)
    (explicitAltCost : Bool := false) (flashback : Option Bool := none)
    (useImplicitPermissions : Bool := true)
    (fromHand : Bool := o.zone == .hand p)
    (excludeIds : Array ObjectId := #[])
    (faceOverride? : Option CardDef := none)
    (castFromZone : Option ZoneKind := none) : Bool :=
  let rawBc := g.baseCard o
  let rawFace := faceOverride?.getD rawBc
  match g.additionalChoiceCostFor? o rawFace with
  | none => true
  | some branches =>
    let env : EvalEnv := { controller := p, sourceId := some o.id }
    branches.any fun branch =>
      branch.items.all fun item =>
        match item with
        | .mana m =>
          let payObj :=
            match faceOverride? with
            | some f =>
              { o with
                id := noSourceSentinelId
                controller := some p
                printed := f
                status := { o.status with faceDown := false } }
            | none => o
          g.canPaySpellCostFromSources p payObj
            (g.playManaCost { o with controller := some p } rawFace m
              (origPerm := origPerm) (flashback := flashback)
              (explicitAltCost := explicitAltCost)
              (useImplicitPermissions := useImplicitPermissions))
            (fromHand := fromHand) (excludeIds := excludeIds) (castFromZone := castFromZone)
        | .behold quality =>
          (g.permanentsOf p).any (fun perm => g.hasSubtype perm quality) ||
            (g.player p).hand.any (fun id =>
              id != o.id && (g.findObject? id).any (fun card => isDiscardableCard card && g.hasSubtype card quality))
        | .sacrifice _ (.filter pred) =>
          (g.permanentsOf p).any (fun perm =>
            perm.id != o.id && EvalExpr.evalObjectPred g env (.live perm) pred)
        | .discard _ .hand =>
          (g.discardableHandIds p).any (fun id => id != o.id)
        | .discard _ (.matching pred) =>
          (g.discardableHandIds p).any (fun id =>
            id != o.id && (g.findObject? id).any (fun c => EvalExpr.evalObjectPred g env (.live c) pred))
        | _ => true

/-- Whether `p` can pay `cost` for activated ability `ab` on `o` from their
current mana pool plus plain tap mana sources, excluding `excludeIds`
(CR 106.1,6 / 602.2b). -/
def canPayAbilityCostFromSources (g : Game) (p : PlayerId) (o : GameObject)
    (ab : ActivatedAbility) (cost : ManaCost)
    (isTurnFaceUp : Bool := false)
    (excludeIds : Array ObjectId := #[])
    (prop? : Option ProposedSpell := none) : Bool :=
  let spend : ManaSpend :=
    if isTurnFaceUp then {}
    else ManaSpend.forAbility (g.types o) (g.supertypes o) (g.subtypes o) (equip := ab.isEquip)
  let sources :=
    ((g.manaSources p).filter (fun (src, _) => !excludeIds.contains src.id)).toList
  g.canPayFromSources (g.player p).manaPool cost sources spend (prop? := prop?)

/-- Whether `p` can legally propose and afford casting `o` face down via Morph `{3}`
(CR 702.37a,c / 708.2), accounting for `CastSpell`'s `prepareSource` precedence
(when `o` is a prepared copy whose front face is castable, `Action.cast o.id` casts
the prepared front-face copy rather than opening Morph `{3}`). -/
def canCastAndPayMorphFaceDown (g : Game) (p : PlayerId) (o : GameObject)
    (excludeIds : Array ObjectId := #[]) : Bool :=
  let bc := g.baseCard o
  let kwFace := { bc with keywords := g.currentKeywords o }
  let preparedBlocksMorph :=
    o.zone == .exile &&
      ((g.playPermissionFor? p o (face? := some bc)).bind (·.prepareSource)).isSome &&
      g.canCastFrontFace p o
  kwFace.kicker.isNone && !preparedBlocksMorph && g.canCastMorphFaceDown p o &&
    let morphObj :=
      { o with
        id := noSourceSentinelId
        controller := some p
        printed := morphSpellFace
        adventurerCard := none
        status := { o.status with faceDown := true } }
    let payMorph (perm? : Option PlayPermission) : Bool :=
      let cost :=
        g.playManaCost morphObj morphSpellFace
          (origPerm := perm?) (flashback := some false)
          (explicitAltCost := true) (useImplicitPermissions := false)
      g.canPaySpellCostFromSources p morphObj cost
        (fromHand := o.zone == .hand p) (excludeIds := excludeIds)
    if o.zone == .exile then
      let perms := g.playPermissionsFor p o
      let cleanPerms :=
        perms.filter fun pm =>
          !pm.withoutManaCost && !pm.payLifeEqualManaValue && pm.prepareSource.isNone &&
            (pm.ignoreTiming || g.timingAllowsCast p morphSpellFace)
      let nullPerm : Option PlayPermission :=
        if g.mayCastExiledBySource p o then some { player := p, anyMana := true } else none
      cleanPerms.any (fun pm => payMorph (some pm)) ||
        ((perms.isEmpty || g.mayCastExiledBySource p o) &&
          g.timingAllowsCast p morphSpellFace && payMorph nullPerm)
    else
      payMorph none

/-- Whether `p` can legally propose and afford casting `o` via its Impending
alternative cost (CR 118.9a / 601.1a / 702.176a), accounting for `prepareSource`
and Flashback precedence in `CastSpell`. -/
def canCastAndPayImpending (g : Game) (p : PlayerId) (o : GameObject)
    (excludeIds : Array ObjectId := #[]) : Bool :=
  let bc := g.baseCard o
  let kwFace := { bc with keywords := g.currentKeywords o }
  match kwFace.morph, kwFace.impending, kwFace.kicker with
  | none, some (_, alt), none =>
    let fromGraveyard := o.zone == .graveyard o.owner
    let isFlashbackCast := fromGraveyard && (kwFace.flashback.isSome || g.flashbackUntilEot o)
    let preparedBlocksImpending :=
      o.zone == .exile &&
        ((g.playPermissionFor? p o (face? := some bc)).bind (·.prepareSource)).isSome
    !isFlashbackCast && !preparedBlocksImpending && g.canCastFrontFace p o &&
      let casterObj := { o with controller := some p }
      let impFace := { bc with manaCost := alt }
      let payImpending (perm? : Option PlayPermission) : Bool :=
        let cost :=
          g.playManaCost casterObj impFace
            (origPerm := perm?) (flashback := some false)
            (explicitAltCost := true) (useImplicitPermissions := false)
        g.canPaySpellCostFromSources p o cost
          (fromHand := o.zone == .hand p) (excludeIds := excludeIds) &&
          g.canPayAnnouncedAdditionalFromSources p o
            (origPerm := perm?) (explicitAltCost := true)
            (flashback := some false) (useImplicitPermissions := false)
            (fromHand := o.zone == .hand p) (excludeIds := excludeIds)
            (faceOverride? := some impFace)
      let perms := g.playPermissionsFor p o
      let hasNullSummoner := o.zone == .exile && g.mayCastExiledBySource p o
      if perms.isEmpty && !hasNullSummoner then
        g.timingAllowsCast p impFace (card? := some o) && payImpending none
      else
        let cleanPerms :=
          perms.filter fun pm =>
            !pm.withoutManaCost && !pm.payLifeEqualManaValue && pm.prepareSource.isNone &&
              (pm.ignoreTiming || g.timingAllowsCast p impFace (card? := some o))
        let nullPerm : Option PlayPermission :=
          if hasNullSummoner then some { player := p, anyMana := true } else none
        cleanPerms.any (fun pm => payImpending (some pm)) ||
          (hasNullSummoner && g.timingAllowsCast p impFace (card? := some o) && payImpending nullPerm)
  | _, _, _ => false

/-- True when the CR 716.3d exile permission forbids recasting as an Adventure. -/
def adventureExileForbidsRecast (g : Game) (o : GameObject)
    (player? : Option PlayerId := none) : Bool :=
  match player? with
  | some p =>
    let perms := g.playPermissionsFor p o
    !perms.isEmpty && perms.all (·.fromAdventure) && !g.mayCastExiledBySource p o
  | none =>
    if g.livingPlayers.any (fun pl => g.mayCastExiledBySource pl.id o) then
      false
    else
      let perms := g.activePlayPermissions o
      if perms.isEmpty then
        (g.playPermission o).any (·.fromAdventure)
      else
        perms.all (·.fromAdventure)

/-- Select a continuous `.playFromExile` (or `mayCastExiledBySource`) permission
for a one-shot paid resolution cast (`!withoutManaCost` / `!withoutPaying`) only
when timing-legal and strictly improving over the resolving effect's clean
permission (`withoutManaCost` > payable `payLifeEqualManaValue` > `anyMana` >
`ignoreTiming` > `!fromAdventure`), preserving resolution `ignoreTiming` and
never picking an unpayable `payLifeEqualManaValue` grant (CR 601.1a / 608.2g / 119.4). -/
def paidResolutionOrigPerm? (g : Game) (p : PlayerId) (o : GameObject)
    (ignoreTiming : Bool := true) (face? : Option CardDef := none) : Option PlayPermission :=
  let isAdv :=
    o.isAdventureSpell ||
      face?.any (fun fc =>
        (g.baseCard o).adventure.any (fun adv =>
          adv.toCardDef == fc || (adv.name == fc.name && fc.name != (g.baseCard o).name)))
  let defaultFace := g.baseCard o
  let f :=
    match face? with
    | some fc => if !isAdv && fc == g.baseCard o then defaultFace else fc
    | none => defaultFace
  let mv :=
    match face? with
    | some fc => if !isAdv && fc == g.baseCard o then g.objectManaValue o else fc.manaCost.manaValue
    | none => g.objectManaValue o
  let timingOk := g.timingAllowsCast p f (ignorePending := true) (card? := some o)
  let nullPerm? : Option PlayPermission :=
    if o.zone == .exile && g.mayCastExiledBySource p o && timingOk then
      some { player := p, anyMana := true }
    else none
  let cands :=
    ((g.playPermissionsFor p o).filter fun pm =>
      pm.prepareSource.isNone &&
        (!isAdv || !pm.fromAdventure) &&
        (pm.ignoreTiming || timingOk) &&
        (pm.withoutManaCost ||
          (pm.payLifeEqualManaValue && g.canPayLife p mv) ||
          (!pm.payLifeEqualManaValue && (pm.anyMana || (!ignoreTiming && pm.ignoreTiming))))) ++
      nullPerm?.toArray
  let rank (pm : PlayPermission) : Nat :=
    (if pm.withoutManaCost then 16 else 0) +
      (if pm.payLifeEqualManaValue then 8 else 0) +
      (if pm.anyMana then 4 else 0) +
      (if pm.ignoreTiming then 2 else 0) +
      (if !pm.fromAdventure then 1 else 0)
  cands.foldl (fun best? pm =>
    match best? with
    | none => some pm
    | some b => if rank pm >= rank b then some pm else some b) none

/-- Whether `prop` was proposed under a forced one-shot free cost
(`.alternative "withoutManaCost"` or `.alternative "free copy"`), forbidding
choosing another alternative cost such as Morph or Impending (CR 118.9a / 707.10f). -/
def isForcedWithoutManaCostProposal (g : Game) (prop : ProposedSpell) : Bool :=
  g.events.reverse.findSome? (fun ev =>
    match ev.change with
    | .rules (.cast (.proposed sid _ _ w)) =>
      if sid == prop.spellId then
        some (w == .alternative "withoutManaCost" || w == .alternative "free copy")
      else none
    | _ => none) |>.getD false

/-- Single timing-legal clean `PlayPermission` (if needed, or `some none` when
casting from a zone that requires no `.playFromExile` grant) for casting `prop`
with alternative face `altFace` (Morph or Impending; CR 118.9a / 601.1a / 702.37a). -/
def proposalAltCleanPerm? (g : Game) (prop : ProposedSpell) (altFace : CardDef) :
    Option (Option PlayPermission) :=
  match g.findObject? prop.spellId with
  | none => none
  | some spell =>
    if prop.sneakAttacker.isSome ||
        GameEvent.castWithFlashback g.events prop.spellId ||
        (prop.origPerm.bind (·.prepareSource)).isSome ||
        g.isForcedWithoutManaCostProposal prop then
      none
    else
      let p := prop.caster
      let preSpell := { spell with
        id := prop.original.id
        zone := prop.original.zone
        exiledBy := prop.original.exiledBy
        controller := some p }
      let baseAltTimingOk :=
        g.timingAllowsCast p altFace (excludeStackId := some prop.spellId) (card? := some spell)
      let allExilePerms := g.playPermissionsFor p preSpell
      let contClean :=
        allExilePerms.filter fun pm =>
          !pm.withoutManaCost && !pm.payLifeEqualManaValue && pm.prepareSource.isNone
      let hasNullSummoner := preSpell.zone == .exile && g.mayCastExiledBySource p preSpell
      let nullClean : Array PlayPermission :=
        if hasNullSummoner then #[{ player := p, anyMana := true }] else #[]
      let resClean : Array PlayPermission :=
        if prop.resolutionCast then
          #[{ player := p, ignoreTiming := prop.resolutionIgnoreTiming }]
        else #[]
      let needsCleanPerm := !allExilePerms.isEmpty || prop.resolutionCast || hasNullSummoner
      if !needsCleanPerm then
        if baseAltTimingOk then some none else none
      else
        let allClean := contClean ++ nullClean ++ resClean
        let timingLegalClean :=
          allClean.filter (fun pm => pm.ignoreTiming || baseAltTimingOk)
        if timingLegalClean.isEmpty then none
        else
          let rank (q : PlayPermission) : Nat :=
            (if q.anyMana then 4 else 0) +
              (if q.ignoreTiming then 2 else 0) +
              (if !q.fromAdventure then 1 else 0)
          let best :=
            timingLegalClean.foldl (fun best? q =>
              match best? with
              | none => some q
              | some b => if rank q >= rank b then some q else some b) none
          some best

/-- Whether `prop` may legally offer choosing Morph at CR 601.2b (CR 118.9a / 702.37a). -/
def proposalCanChooseMorph (g : Game) (prop : ProposedSpell) : Bool :=
  match g.findObject? prop.spellId with
  | none => false
  | some spell =>
    let face := { g.baseCard spell with keywords := g.currentKeywords spell }
    face.morph.isSome && face.kicker.isNone &&
      prop.original.zone != .graveyard prop.original.owner &&
      !g.spellNameForbidden "" &&
      (g.proposalAltCleanPerm? prop morphSpellFace).isSome

/-- Whether `prop` may legally offer choosing Impending at CR 601.2b (CR 118.9a / 702.176a). -/
def proposalCanChooseImpending (g : Game) (prop : ProposedSpell) : Bool :=
  match g.findObject? prop.spellId with
  | none => false
  | some spell =>
    let rawFace := g.baseCard spell
    let kwFace := { rawFace with keywords := g.currentKeywords spell }
    match kwFace.impending, kwFace.kicker with
    | some (_, alt), none =>
      (g.proposalAltCleanPerm? prop { rawFace with manaCost := alt }).isSome
    | _, _ => false


/-- Validate front-face timing, prohibitions, targets, and mandatory additional
costs when casting `card` as `face` (either upfront in `castSpell` or when
choosing the printed cost instead of Morph at `announceKicker`; CR 601.2b–c /
601.3 / 702.37a). -/
def validateFrontFaceCast (g : Game) (p : PlayerId) (card : GameObject) (face : CardDef)
    (sneakCost : Option ManaCost := none)
    (sneakAttacker : Option ObjectId := none)
    (origPermOverride : Option PlayPermission := none)
    (excludeIdOverride : Option ObjectId := none) : Except String Unit := do
  let checkId := excludeIdOverride.getD card.id
  -- CR 601.3e / 716.3a: an Adventure is cast with only its alternative (Instant /
  -- Sorcery) characteristics, so a creature-only top-of-library permission (Elven Chorus)
  -- can't cast it.
  if card.zone == .library p && !face.isCreature then
    throw "You may only cast creature spells from the top of your library"
  if g.spellNameForbidden face.name then
    throw s!"Spells named {face.name} can't be cast"
  if face.isLand then
    throw "Lands are played, not cast (CR 305)"
  if let some err := g.castRestrictionError? p card.id face then
    throw err
  let perms := g.playPermissionsFor p card
  let anyIgnoreTiming :=
    match origPermOverride with
    | some pm => pm.ignoreTiming
    | none => perms.any (·.ignoreTiming)
  if !(g.timingAllowsCast p face (excludeStackId := excludeIdOverride) (card? := some card) ||
      anyIgnoreTiming || sneakCost.isSome) then
    throw s!"{face.name} has sorcery speed"
  if isModalSpellFace face then
    let tcs := g.evalLayer3 card
    if !(effectiveSpellModes face).any (fun e =>
        let m := if tcs.isEmpty then e else TextChange.applyEffect tcs e
        g.spellModeIsChoosable p m (some checkId)) &&
        !isReturnUpToTwoGyModal face && !face.allowsZeroTargets then
      throw s!"{face.name} requires a target"
  else
    let tcs := g.evalLayer3 card
    let eff? := face.spellEffect.map (fun e =>
      g.expandEachOpponentEffect p (if tcs.isEmpty then e else TextChange.applyEffect tcs e))
    let reqTarget := eff?.map (·.requiresTarget) |>.getD face.requiresTarget
    if reqTarget && !face.allowsZeroTargets &&
        !g.castFaceHasLegalTarget p face tcs (some checkId) then
      throw s!"{face.name} requires a target"
  let gSac :=
    match sneakAttacker with
    | some aid => g.probeAfterSneakReturn p checkId aid
    | none => g
  if let some err := gSac.mandatorySacrificeError? p checkId face then
    throw err

/-- Whether `p` may begin to cast `o` as an Adventure (CR 716.3). -/
def canCastAdventure (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  match (g.baseCard o).adventure with
  | none => false
  | some adv =>
    let face := adv.toCardDef
    let fromGraveyard := o.zone == .graveyard o.owner
    let hadFlashbackPerm := fromGraveyard && g.flashbackUntilEot o
    let isFlashbackCast := fromGraveyard && (face.flashback.isSome || hadFlashbackPerm)
    let perms := g.playPermissionsFor p o
    let advPerms := perms.filter (!·.fromAdventure)
    !g.splitSecondOnStack &&
    !g.combatLocksNonManaAbilities &&
    !g.opponentsCantCastOnActiveTurn p &&
    !g.spellNameForbidden face.name &&
    !g.cantCastSpellsThisTurn p &&
    !g.adventureExileForbidsRecast o (some p) &&
    -- CR 601.3e / 716.3a: the Adventure's own (Instant / Sorcery) characteristics decide
    -- whether a creature-only library-top permission applies.
    (o.zone != .library p || face.isCreature) &&
    g.mayPlay p o &&
    g.graveyardCastThresholdMet p o.id face &&
    (if perms.isEmpty then
      g.timingAllowsCast p face (card? := some o)
     else
      advPerms.any (fun perm =>
        (perm.ignoreTiming || g.timingAllowsCast p face (card? := some o)) &&
          (!perm.payLifeEqualManaValue || g.canPayLife p face.manaValue)) ||
        (g.mayCastExiledBySource p o && g.timingAllowsCast p face (card? := some o))) &&
    (g.mandatorySacrificeError? p o.id face).isNone &&
    (!(isFlashbackCast && face.flashbackDiscard) || (g.discardableHandIds p).any (· != o.id)) &&
    let tcs := g.evalLayer3 o
    if isModalSpellFace face then
      (effectiveSpellModes face).any (fun e =>
        let m := if tcs.isEmpty then e else TextChange.applyEffect tcs e
        g.spellModeIsChoosable p m (some o.id)) ||
        isReturnUpToTwoGyModal face || face.allowsZeroTargets
    else
      let eff? := face.spellEffect.map (fun e =>
        g.expandEachOpponentEffect p (if tcs.isEmpty then e else TextChange.applyEffect tcs e))
      let reqTarget := eff?.map (·.requiresTarget) |>.getD face.requiresTarget
      if reqTarget then
        face.allowsZeroTargets || g.castFaceHasLegalTarget p face tcs (some o.id)
      else true

/-- Whether activating `ch` covers more of `cost` than `pool`. -/
def choiceHelpsPay (pool : ManaPool) (ch : TapManaChoice)
    (cost : ManaCost) (spend : ManaSpend := {}) : Bool :=
  if ch.totalSize == 0 then false
  else
    let covered (pl : ManaPool) := pl.coveredMana cost spend
    covered (ch.applyToPool pool) > covered pool

/-- Whether tapping `src` for `t` covers more of `cost` than the current pool. -/
def typeHelpsPay (g : Game) (p : PlayerId) (src : GameObject) (t : ManaType)
    (cost : ManaCost) (spend : ManaSpend := {}) (prop? : Option ProposedSpell := none) : Bool :=
  let amount := g.manaFromTap src t (prop? := prop?) (spend := spend)
  if amount == 0 then false
  else
    let pool := (g.player p).manaPool
    let covered (pool : ManaPool) := pool.coveredMana cost spend
    covered (g.poolAfterTap pool src t (prop? := prop?) (spend := spend)) > covered pool

/-- Select the best `TapManaChoice` among `choices` for `pool` and `cost`:
prefer single-type `.tapForMana` choices when viable, otherwise mixed-color
`.combination` tuples that cover the most symbols / unmet colors. -/
private def pickViableTapChoice (pool : ManaPool) (cost : ManaCost)
    (spend : ManaSpend) (viable : Array TapManaChoice) : Option TapManaChoice :=
  if viable.isEmpty then none
  else
    let singleViable := viable.filter (fun (ch : TapManaChoice) => ch.singleTapType?.isSome)
    if !singleViable.isEmpty then
      let first := singleViable[0]!
      match Color.all.findSome? (fun c =>
        let req := cost.coloredCount c
        let held := pool.usable (.colored c) spend
        if held < req then
          singleViable.find? (fun (ch : TapManaChoice) => ch.singleTapType? == some (.colored c))
        else none) with
      | some ch => some ch
      | none =>
        (singleViable.find? (fun (ch : TapManaChoice) => ch.singleTapType? == some .colorless)).orElse
          (fun _ => some first)
    else
      let covered (pl : ManaPool) := pl.coveredMana cost spend
      viable.foldl (fun best? (ch : TapManaChoice) =>
        match best? with
        | none => some ch
        | some b =>
          if covered (ch.applyToPool pool) > covered (b.applyToPool pool) then some ch
          else some b) none

/-- Best `TapManaChoice` on `(src, types)` that helps pay `cost` (including
mixed-color `.combination` tuples when no single-color tap leaves `others`
payable). -/
def preferredManaChoice (g : Game) (p : PlayerId) (src : GameObject)
    (types : Array ManaType) (cost : ManaCost)
    (others : List (GameObject × Array ManaType) := []) (spend : ManaSpend := {})
    (prop? : Option ProposedSpell := none) : Option TapManaChoice :=
  let pool := (g.player p).manaPool
  let allChoices := g.tapChoicesForSource src types cost (prop? := prop?) (spend := spend)
  let helpful := allChoices.filter (fun (ch : TapManaChoice) =>
    choiceHelpsPay pool ch cost spend)
  let payable :=
    g.canPayFromSources pool cost ((src, types) :: others) spend prop?
  let viable :=
    if payable then
      helpful.filter (fun (ch : TapManaChoice) =>
        g.canPayFromSources (ch.applyToPool pool) cost others spend prop?)
    else helpful
  pickViableTapChoice pool cost spend viable

/-- A mana type among `types` that helps pay remaining symbols of `cost`.
When `src` plus `others` can pay, types that would make the cost unpayable
are omitted so Hidden Lair taps for `{U}` or `{B}` instead of a color another
source already covers. Prefers an unmet colored requirement, then colorless
if it can be spent. -/
def preferredManaType (g : Game) (p : PlayerId) (src : GameObject)
    (types : Array ManaType) (cost : ManaCost)
    (others : List (GameObject × Array ManaType) := []) (spend : ManaSpend := {}) :
    Option ManaType :=
  (g.preferredManaChoice p src types cost others spend).map
    TapManaChoice.primaryType

/-- Whether `(src, t)` is a better next tap than `(bestSrc, bestT)`: avoid
creatures (and artifacts when `avoidArtifacts` is set) when another source
helps, then prefer colorless. Equal ranks keep the earlier source. -/
def betterManaTap (g : Game) (src : GameObject) (t : ManaType)
    (bestSrc : GameObject) (bestT : ManaType) (avoidArtifacts : Bool := false) : Bool :=
  let penalize (o : GameObject) : Bool :=
    g.isCreature o || (avoidArtifacts && g.isArtifact o)
  (!penalize src && penalize bestSrc) ||
    (penalize src == penalize bestSrc && !g.isCreature src && g.isCreature bestSrc) ||
    (penalize src == penalize bestSrc && g.isCreature src == g.isCreature bestSrc &&
      t == .colorless && bestT != .colorless)

/-- Permanents `p` may sacrifice to pay “sacrifice another creature or artifact”. -/
def sacrificeCreatureOrArtifactChoices (g : Game) (p : PlayerId) (sourceId : ObjectId) :
    Array GameObject :=
  let src := g.findObject? sourceId
  let isSpellSource (s : GameObject) : Bool :=
    s.zone == .stack && g.proposedSpell.all (fun pr => pr.spellId != sourceId || pr.kind == .spell)
  let pred? := src.bind fun s =>
    if isSpellSource s then g.spellSacrificeCostPredFor? s (g.baseCard s) else none
  match pred? with
  | some pred =>
    let env : EvalEnv := { controller := p, sourceId := some sourceId }
    g.permanentsOf p |>.filter fun o =>
      o.id != sourceId && EvalExpr.evalObjectPred g env (.live o) pred
  | none =>
    g.permanentsOf p |>.filter fun o =>
      o.id != sourceId && (g.isCreature o || g.isArtifact o)

/-- Whether tapping `preTappedIds` for mana leaves `prop`'s unpaid post-mana
costs payable (teamwork, behold, sneak-excluded sacrifice, discard, `.crew`,
`.zemoBoast`, and `CostPick`s; CR 601.2g–h / 602.2b). -/
def tapPreservesPostManaCosts (g : Game) (p : PlayerId) (prop : ProposedSpell)
    (preTappedIds : Array ObjectId) : Bool :=
  let teamworkOk :=
    !prop.teamworkPaid || prop.teamworkCreatures.isEmpty ||
      prop.teamworkCreatures.all fun id =>
        !preTappedIds.contains id &&
          (g.findObject? id).any fun o =>
            o.isOnBattlefield && g.isCreature o && g.controlledBy o p && !o.status.tapped
  let beholdOk :=
    match prop.needsBehold with
    | none => true
    | some quality =>
      (g.permanentsOf p).any (fun o => g.hasSubtype o quality) ||
        (g.player p).hand.any (fun id =>
          id != prop.spellId &&
            (g.findObject? id).any (fun card => isDiscardableCard card && g.hasSubtype card quality))
  if !teamworkOk || !beholdOk then false
  else
    let sinceIdx := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD g.events.size
    let tapSourceOk :=
      !prop.tapSource ||
        match prop.sourceId with
        | none => true
        | some sid =>
          g.sourceTappedForCost sid (some prop.spellId) sinceIdx || !preTappedIds.contains sid
    if !tapSourceOk then false
    else if prop.kind != .activatedAbility then
      let gSneak := g.probeAfterUnpaidSneak prop
      let excludeId := prop.sourceId.getD prop.spellId
      let sacOk :=
        !prop.needsSacrificeOther ||
          !(gSneak.sacrificeCreatureOrArtifactChoices p excludeId).isEmpty
      let discardOk :=
        !prop.needsDiscardCard || (gSneak.discardableHandIds p).any (· != prop.spellId)
      sacOk && discardOk
    else
      match prop.sourceId, prop.activation with
      | some sid, some ab =>
        let basePicks := costPicksOf ab
        let allPicks := costPicksWithSacrificeOther basePicks
          (prop.needsSacrificeOther || ab.cost.sacrificeAnotherCreatureOrArtifact)
        let sacSrc :=
          prop.sacrificeSource || ab.cost.sacrificeSource || ab.cost.exileSourceFromBattlefield
        let discSrc :=
          prop.discardSource || ab.cost.discardSource || ab.cost.exileSourceFromHand
        let zemoOk : Bool :=
          if prop.choiceCostPaid then true
          else
            match ab.cost.exileManaSymbols? with
            | none => true
            | some (col?, minSyms, pred) =>
              g.canPayExileManaSymbols p sid col? minSyms pred
                (excludedIds := if ab.cost.exileSourceFromGraveyard then #[sid] else #[])
        if !zemoOk then false
        else
          let crewN? : Option Nat :=
            if !prop.choiceCostPaid then ab.cost.crewPower? else none
          match crewN? with
          | some n =>
            (g.firstPayableCrewSelection? p sid n allPicks
              (tapSource := prop.tapSource)
              (sacrificeOrExileSource := sacSrc)
              (discardOrExileHandSource := discSrc)
              (preTappedIds := preTappedIds)).isSome
          | none =>
            allPicks.isEmpty ||
              g.costPicksPayable p (some sid) allPicks
                (tapSource := prop.tapSource)
                (sacrificeOrExileSource := sacSrc)
                (discardOrExileHandSource := discSrc)
                (preTappedIds := preTappedIds)
      | _, _ =>
        let excludeId := prop.sourceId.getD prop.spellId
        (!prop.needsSacrificeOther || !(g.sacrificeCreatureOrArtifactChoices p excludeId).isEmpty) &&
          (!prop.needsDiscardCard || !(g.discardableHandIds p).isEmpty)

/-- Whether some subset of `sources` (combined with `preTappedIds` and `pool`)
pays `cost` while preserving `prop?`'s unpaid post-mana `.crew` and tap
`CostPick` costs (CR 601.2g–h). Collapses skipped identical sources so 20+
homogeneous dorks/artifacts never branch exponentially. -/
def hasCostPreservingPaymentSubset (g : Game) (pool : ManaPool) (cost : ManaCost)
    (sources : Array (GameObject × Array ManaType))
    (spend : ManaSpend := {})
    (prop? : Option (PlayerId × ProposedSpell) := none)
    (preTappedIds : Array ObjectId := #[]) : Bool :=
  let activeProp? := prop?.map (·.2)
  let usableSources :=
    sources.filter fun (o, ts) =>
      !(g.tapChoicesForSource o ts cost
        (dedupSingleTypes := fun xs => dedupZeroReqManaTypes g o xs cost activeProp? spend)
        (prop? := activeProp?)
        (spend := spend)).isEmpty
  match prop? with
  | none =>
    g.canPayFromSources pool cost usableSources.toList spend none
  | some (p, prop) =>
    if !g.tapPreservesPostManaCosts p prop preTappedIds then false
    else if g.tapPreservesPostManaCosts p prop (preTappedIds ++ usableSources.map (·.1.id)) then
      g.canPayFromSources pool cost usableSources.toList spend (some prop)
    else
      let allPicks : Array CostPick :=
        if prop.kind != .activatedAbility then #[]
        else
          match prop.activation with
          | some ab =>
            costPicksWithSacrificeOther (costPicksOf ab)
              (prop.needsSacrificeOther || ab.cost.sacrificeAnotherCreatureOrArtifact)
          | none => #[]
      let sacSrc :=
        prop.sacrificeSource ||
          prop.activation.any (fun ab => ab.cost.sacrificeSource || ab.cost.exileSourceFromBattlefield)
      let discSrc :=
        prop.discardSource ||
          prop.activation.any (fun ab => ab.cost.discardSource || ab.cost.exileSourceFromHand)
      let isCrit (o : GameObject) : Bool :=
        g.isCreature o || g.isArtifact o ||
          (prop.tapSource && prop.sourceId == some o.id) ||
          prop.teamworkCreatures.contains o.id ||
          allPicks.any fun pk =>
            match pk with
            | .custom (.tapObjects ..) | .custom (.or _) =>
              g.costPickAllows p prop.sourceId pk o
                (tapSource := prop.tapSource)
                (sacrificeOrExileSource := sacSrc)
                (discardOrExileHandSource := discSrc)
            | _ => false
      let freeOthers := (usableSources.filter (fun (o, _) => !isCrit o)).toList
      let critRem := (usableSources.filter (fun (o, _) => isCrit o)).toList
      let equivKey (o : GameObject) (choices : Array TapManaChoice) :=
        let pickMask :=
          allPicks.map fun pk =>
            g.costPickAllows p prop.sourceId pk o
              (tapSource := prop.tapSource)
              (sacrificeOrExileSource := sacSrc)
              (discardOrExileHandSource := discSrc)
        (some o.id == prop.sourceId, o.attachedTo == prop.sourceId,
          prop.teamworkCreatures.contains o.id,
          g.isCreature o, g.isArtifact o, g.power o, pickMask,
          choices.map (fun (ch : TapManaChoice) => (ch.baseAdded, ch.extraRed, ch.restriction, ch.riders)))
      let rec go (curPool : ManaPool) (chosenIds : Array ObjectId)
          (skippedKeys : Array (Bool × Bool × Bool × Bool × Bool × Int × Array Bool ×
            Array (Array ManaType × Array ManaUnit × Option ManaSpendRestriction × Array SpellRiderSpec)))
          (rem : List (GameObject × Array ManaType)) : Bool :=
        if !g.tapPreservesPostManaCosts p prop chosenIds then false
        else if g.canPayFromSources curPool cost freeOthers spend activeProp? then true
        else if !g.canPayFromSources curPool cost (rem ++ freeOthers) spend activeProp? then false
        else
          match rem with
          | [] => false
          | (o, ts) :: rest =>
            let choices :=
              g.tapChoicesForSource o ts cost
                (dedupSingleTypes := fun xs => dedupZeroReqManaTypes g o xs cost activeProp? spend)
                (prop? := activeProp?)
                (spend := spend)
            let k := equivKey o choices
            let tryTap :=
              !skippedKeys.contains k &&
                choices.any (fun (ch : TapManaChoice) =>
                  go (ch.applyToPool curPool) (chosenIds.push o.id) skippedKeys rest)
            tryTap || go curPool chosenIds (if skippedKeys.contains k then skippedKeys else skippedKeys.push k) rest
      go pool preTappedIds #[] critRem

/-- Next plain `{T}` mana choice to activate for `prop` (supporting both
`.tapForMana` single-type taps and mixed-color `.combination` tuples via
`.activateManaAbility`). -/
def preferredManaTapChoice (g : Game) (p : PlayerId) (prop : ProposedSpell) :
    Option (GameObject × TapManaChoice) :=
  let spend := g.proposedManaSpend prop
  let sources := g.manaSourcesForProposed p prop
  let pool := (g.player p).manaPool
  let avoidArtifacts : Bool :=
    prop.kind == .activatedAbility &&
      prop.activation.any (fun ab => (costPicksOf ab).contains .tapTwoUntappedArtifacts)
  let allPreserve := g.tapPreservesPostManaCosts p prop (sources.map (·.1.id))
  let allPay := g.canPayFromSources pool prop.cost sources.toList spend (some prop)
  let fullPick? : Option (GameObject × TapManaChoice) :=
    if !allPay then none
    else
      sources.foldl (fun acc (src, types) =>
        let choices := g.tapChoicesForSource src types prop.cost (prop? := some prop) (spend := spend)
        let helpful := choices.filter (fun (ch : TapManaChoice) =>
          choiceHelpsPay pool ch prop.cost spend)
        if helpful.isEmpty then acc
        else
          let othersArr := sources.filter (fun (o, _) => o.id != src.id)
          let viable :=
            if allPreserve then
              helpful.filter (fun (ch : TapManaChoice) =>
                g.canPayFromSources (ch.applyToPool pool) prop.cost
                  othersArr.toList spend (some prop))
            else
              helpful.filter (fun (ch : TapManaChoice) =>
                g.hasCostPreservingPaymentSubset (ch.applyToPool pool) prop.cost
                  othersArr spend (some (p, prop)) #[src.id])
          match pickViableTapChoice pool prop.cost spend viable with
          | none => acc
          | some ch =>
            match acc with
            | none => some (src, ch)
            | some (bestSrc, bestCh) =>
              if g.betterManaTap src ch.primaryType bestSrc bestCh.primaryType (avoidArtifacts := avoidArtifacts) then
                some (src, ch)
              else acc) none
  fullPick?.orElse fun _ =>
    let safeSources := sources.filter (fun (src, _) => g.tapPreservesPostManaCosts p prop #[src.id])
    let pickFrom (candSources : Array (GameObject × Array ManaType))
        (poolSources : Array (GameObject × Array ManaType)) : Option (GameObject × TapManaChoice) :=
      candSources.foldl (fun acc (src, types) =>
        let others := poolSources.filter (fun (o, _) => o.id != src.id) |>.toList
        match g.preferredManaChoice p src types prop.cost others spend (some prop) with
        | none => acc
        | some ch =>
          match acc with
          | none => some (src, ch)
          | some (bestSrc, bestCh) =>
            if g.betterManaTap src ch.primaryType bestSrc bestCh.primaryType (avoidArtifacts := avoidArtifacts) then
              some (src, ch)
            else acc) none
    (if safeSources.isEmpty then none else pickFrom safeSources safeSources).orElse
      (fun _ => pickFrom sources sources)

/-- Next source to tap for `prop`. Noncreatures (and non-artifacts when
`.tapTwoUntappedArtifacts` is unpaid) are chosen before creatures/artifacts
when both help, and colorless is preferred when that type can be spent.
A flexible source such as Hidden Lair is tapped for `{U}` or `{B}` when
that choice still lets the remaining sources pay. Sources are restricted to
subsets whose combined mana plus `(g.player p).manaPool` pays `prop.cost`
while preserving unpaid `.crew` and tap `CostPick`s whenever such a subset
exists (CR 601.2g–h). -/
def preferredManaTap (g : Game) (p : PlayerId) (prop : ProposedSpell) :
    Option (GameObject × ManaType) :=
  (g.preferredManaTapChoice p prop).map (fun (src, ch) => (src, ch.primaryType))


def payCost (g : Game) (p : PlayerId) (cost : ManaCost)
    (spend : ManaSpend := {})
    (forObject : Option ObjectId := none) :
    Except String Game := do
  let pl := g.player p
  match pl.manaPool.payUnits? cost spend with
  | none => throw s!"{pl.name} cannot pay {cost}"
  | some (_, spentUnits) =>
    return g.record
      (GameEvent.manaSpent g.turnNumber p spentUnits forObject
        (cause := some (.costPayment .mana p forObject)))

/-- Run any deferred mid-resolution post-cast cleanup (`PostCastCleanup`) once
a cast-during-resolution spell finishes casting (`becomeCast`) or reverses
(`reverseProposedSpellCore?`). -/
@[export mtg_game_run_post_cast_cleanup]
def runPostCastCleanup (g : Game) : Game :=
  match g.postCastCleanup with
  | none => g
  | some cleanup =>
    let g := g.change (.postCastCleanup none)
    match cleanup with
    | .cascadeBottom caster cardId others =>
      if !g.stillInGame caster then g
      else
        let cause := g.lastMoveCauseOf? cardId
        let landed := g.followMoved cardId
        let cast := (g.findObject? landed).any (·.zone == .stack)
        let bottomed := if cast then others else others.push cardId
        let msg :=
          if cast then
            s!"{(g.player caster).name} puts the other exiled cards on the bottom of their library in a random order"
          else
            s!"{(g.player caster).name} puts the exiled cards on the bottom of their library in a random order"
        g.requestOrderInto bottomed (.library caster) msg (cause := cause)
    | .grimaBottom victim cardId others =>
      if !g.stillInGame victim then g
      else
        let cause := g.lastMoveCauseOf? cardId
        let landed := g.followMoved cardId
        let cast := (g.findObject? landed).any (·.zone == .stack)
        let uncast :=
          if cast then #[]
          else if (g.findObject? cardId).any (·.zone == .exile) then #[cardId]
          else if (g.findObject? landed).any (·.zone == .exile) then #[landed]
          else #[]
        let pile := (others ++ uncast).filter (fun id => (g.findObject? id).any (·.zone == .exile))
        let msg :=
          s!"{(g.player victim).name} puts the exiled cards that weren't cast on the bottom of their library in a random order"
        g.requestOrderInto pile (.library victim) msg (cause := cause)
    | .copyCeaseToExist copyId =>
      let landed := g.followMoved copyId
      let onStack :=
        (g.findObject? landed).any (·.zone == .stack) ||
          (g.findObject? copyId).any (·.zone == .stack)
      if onStack then g
      else
        let copyCause := some (EventCause.stateBased .copyOutsideStackOrBf)
        match g.findObject? copyId with
        | some o =>
          if o.isCopy then
            let objName := g.name o
            (g.ceaseToExist o.id (cause := copyCause)).logMsg s!"The copy of {objName} ceases to exist"
          else g
        | none =>
          match g.findObject? landed with
          | some o =>
            if o.isCopy then
              let objName := g.name o
              (g.ceaseToExist o.id (cause := copyCause)).logMsg s!"The copy of {objName} ceases to exist"
            else g
          | none => g
    | .lookedBottom caster cardId allLooked =>
      if !g.stillInGame caster then g
      else
        let landed := g.followMoved cardId
        let cast := (g.findObject? landed).any (·.zone == .stack)
        let unchosen :=
          (if cast then allLooked.filter (· != cardId) else allLooked).filter (fun id =>
            (g.findObject? id).any (·.zone == .library caster))
        if unchosen.isEmpty then g
        else
          let msg :=
            s!"{(g.player caster).name} puts the rest on the bottom of their library in a random order"
          g.requestOrderInto unchosen (.library caster) msg

/-- Core proposal reversal: restores `proposalCheckpoint`, reapplies CR 734.1
irreversible library actions, runs deferred `postCastCleanup`, and reports
whether `Decisions.finishResolutionChoice` should resume an active continuation
(CR 601.2 / 602.2 / 734.1–734.2). -/
def reverseProposedSpellCore? (g : Game) (resumeContinuation : Bool := false)
    (extraLog : Option String := none)
    (alwaysGrantPriority : Bool := false)
    (skipDepartureReconcile : Bool := false)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Except String (Game × Bool) := do
  match g.proposedSpell with
  | none => return (g, false)
  | some prop =>
    let g := g.popNestedManaProposalCheckpoint
    let name := (g.player prop.caster).name
    let baseTriggers := (g.proposalCheckpoint.map (·.waitingTriggers.size)).getD 0
    let baseEventSize := (g.proposalCheckpoint.map (·.eventsSize)).getD g.events.size
    let allDeparted : Array PlayerId :=
      match g.proposalCheckpoint with
      | some ckpt => g.playersDepartedSinceCheckpoint ckpt
      | none => #[]
    let doReconcileDep := !skipDepartureReconcile && !allDeparted.isEmpty
    let ckptPending : Pending := (g.proposalCheckpoint.map (·.pending)).getD .none
    let ckptOrigCont? : Option PendingReplacement :=
      g.proposalCheckpoint.bind fun ckpt =>
        (ckpt.continuations.back?.getD {}).pendingReplacement
    let ckptOuters : Array PendingReplacement :=
      g.proposalCheckpoint.map (fun ckpt =>
        (ckpt.continuations.back?.getD {}).outerPendingReplacements) |>.getD #[]
    let preRewindOuters : Array PendingReplacement := g.outerPendingReplacements
    let ckptMovedToOuter : Bool :=
      if !doReconcileDep then false
      else
        g.proposalCheckpoint.any fun ckpt =>
          ((ckpt.continuations.back?.getD {}).pendingReplacement).any fun ckptCont => Id.run do
            let slice := g.events.extract (min ckpt.eventsSize g.events.size) g.events.size
            for ev in slice do
              match ev with
              | .engine _ (.continuation (.pushOuterPendingReplacement pushed)) _ =>
                if pushed == ckptCont then return true
              | .engine _ (.beginProposalAction _) _
              | .engine _ (.proposedSpell (some _)) _
              | .engine _ (.continuation .popOuterPendingReplacement) _
              | .rules _ (.player (.lost ..)) _ _
              | .rules _ (.player (.leftGame ..)) _ _ =>
                return false
              | _ => pure ()
            return false
    let ckptUntouchedBeforeLeave : Bool :=
      if !doReconcileDep then false
      else
        g.proposalCheckpoint.any fun ckpt =>
          g.ckptPendingReplacementUntouchedBeforeLeave ckpt allDeparted
    let hadConsumedOrig : Bool :=
      ckptOrigCont?.isSome && !(ckptMovedToOuter || ckptUntouchedBeforeLeave)
    let startExtraIdx :=
      if ckptMovedToOuter && ckptOuters.size < preRewindOuters.size then
        ckptOuters.size + 1
      else
        ckptOuters.size
    let extraDepartureOuters : Array PendingReplacement :=
      if doReconcileDep && startExtraIdx < preRewindOuters.size then
        (preRewindOuters.extract startExtraIdx preRewindOuters.size).map
          (PendingReplacement.appendDepartedMany allDeparted)
      else #[]
    let reversed :=
      match prop.kind with
      | .spell => "the casting is reversed (CR 601.2 / 734.1)"
      | .activatedAbility => "the activation is reversed (CR 602.2 / 734.1)"
      | .turnFaceUp => "turning it face up is reversed (CR 116.2b / 702.37e / 734.1)"
    let wasSuppressed := g.suppressInteractiveReplay
    let g ← g.reverseToProposalCheckpoint?
    let quiet := wasSuppressed || g.suppressInteractiveReplay
    let hasUnreversedActions := g.events.size > baseEventSize
    let g := g.logMsg s!"{name} cannot pay {prop.cost}; {reversed}"
    let g :=
      match extraLog with
      | some msg => g.logMsg msg
      | none => g
    let g := if g.over || quiet then g else g.runPostCastCleanup
    let g :=
      if !doReconcileDep || g.over then g
      else Id.run do
        let seqOpt (a? b? : Option PendingReplacement) : Option PendingReplacement :=
          match a?, b? with
          | some a, some b => some (.seq a b)
          | some a, none => some a
          | none, some b => some b
          | none, none => none
        let mut g :=
          match ckptOrigCont?, g.pendingReplacement with
          | some origCont, some curCont =>
            let stripped? := PendingReplacement.dropTargetModDeparted origCont curCont
            if stripped? != some curCont then g.change (.pendingReplacement stripped?) else g
          | _, _ => g
        let rawCkptRestoreTarget : Option PendingReplacement :=
          if ckptPending != .none then some (.restorePending ckptPending false) else none
        let mut strippedDeferredCkptPending := false
        if let some target := rawCkptRestoreTarget then
          if let some curCont := g.pendingReplacement then
            if PendingReplacement.containsModDeparted target curCont then
              let stripped? := PendingReplacement.dropTargetModDeparted target curCont
              if stripped? != some curCont then
                g := g.change (.pendingReplacement stripped?)
              strippedDeferredCkptPending := true
        if !g.over && g.afterRandom.player?.any (fun r => allDeparted.contains r || !g.stillInGame r) then
          g := g.change (.afterRandom .none)
        if hadConsumedOrig && g.pending == .none && g.afterRandom == .none then
          while g.continuations.back? == some {} do
            g := g.change .popContinuationFrame
        g := g.appendDepartedManyToContinuations allDeparted
        let keepOrigCont? : Option PendingReplacement :=
          if ckptMovedToOuter || ckptUntouchedBeforeLeave then
            match (if ckptMovedToOuter && ckptOuters.size < preRewindOuters.size then
                     some preRewindOuters[ckptOuters.size]!
                   else ckptOrigCont?).map (·.appendDepartedMany allDeparted) with
            | some origDep =>
              if extraDepartureOuters.any (PendingReplacement.containsModDeparted origDep) then
                none
              else some origDep
            | none => none
          else none
        let extraToPush : Array PendingReplacement :=
          if ckptMovedToOuter && !extraDepartureOuters.isEmpty then
            match keepOrigCont? with
            | some keepOrig =>
              extraDepartureOuters.set! 0 (.seq extraDepartureOuters[0]! keepOrig)
            | none => extraDepartureOuters
          else
            extraDepartureOuters
        if !extraToPush.isEmpty then
          if g.continuations.isEmpty then
            g := g.change (.pushContinuationFrame {})
          g := extraToPush.foldl (fun acc o => acc.change (.pushOuterPendingReplacement o)) g
        let restored? : Option PendingReplacement :=
          if ckptMovedToOuter && !extraDepartureOuters.isEmpty then none else keepOrigCont?
        let mut restoreCkptPending? : Option PendingReplacement := none
        if !g.sbaPaused && ckptPending != .none && g.pending == ckptPending then
          g := g.change (.pending .none)
          restoreCkptPending? := some (.restorePending ckptPending false none allDeparted none)
        else if strippedDeferredCkptPending then
          restoreCkptPending? := some (.restorePending ckptPending false none allDeparted none)
        let ckptWasRandom : Bool :=
          match ckptPending with | .resolveRandom _ => true | _ => false
        let freshCont? := g.pendingReplacement
        if !quiet && !g.sbaPaused && g.pending == .none &&
            (g.afterRandom == .none || (ckptWasRandom && restoreCkptPending?.isSome)) &&
            freshCont?.isNone then
          if let some rp := restoreCkptPending? then
            g := g.resumePendingReplacementFwd rp
          if !g.over then
            if let some rest := restored? then
              if g.continuations.isEmpty then
                g := g.change (.pushContinuationFrame {})
              if g.pendingReplacement != some rest then
                g := g.chainPendingReplacement rest
          if g.pending == .none && g.afterRandom == .none && g.pendingReplacement.isNone then
            while g.continuations.back? == some {} do
              g := g.change .popContinuationFrame
          return g
        else
          let combinedCont? := seqOpt freshCont? (seqOpt restoreCkptPending? restored?)
          match combinedCont? with
          | some combined =>
            if g.continuations.isEmpty then
              g := g.change (.pushContinuationFrame {})
            if g.pendingReplacement != some combined then
              g := g.change (.pendingReplacement (some combined))
          | none =>
            if g.pendingReplacement.isSome then
              g := g.change (.pendingReplacement none)
            if g.pending == .none && g.afterRandom == .none then
              while g.continuations.back? == some {} do
                g := g.change .popContinuationFrame
          return g
    if quiet || g.suppressInteractiveReplay then
      return (g, false)
    let explicitPrio? : Option PlayerId :=
      if followedByFinishChoice then none else followedByExplicitPriority?
    let prio := g.priorityInstead (explicitPrio?.getD prop.caster)
    let stashPendingPrio (g : Game) : Game :=
      if g.pendingPriority == some prio then g
      else g.change (.pendingPriority (some prio))
    if g.over then
      return (g.receivePriority prio, false)
    if followedByFinishChoice && g.sbaPaused then
      let g :=
        if let some cur := g.pendingReplacement then
          let next := cur.ensureEndsWithFinishResolutionChoice
          if next == cur then g else g.change (.pendingReplacement (some next))
        else
          let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
          g.change (.pendingReplacement (some .finishResolutionChoice))
      return (g, false)
    if explicitPrio?.isSome then
      if g.sbaPaused then
        let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
        let g :=
          if g.pendingReplacement.any (·.endsWithPriorityGrant) then
            if g.pendingReplacement.any g.continuationUsesImplicitPendingPriorityFwd then
              stashPendingPrio g
            else g
          else
            let g :=
              if g.pendingReplacement.any g.continuationUsesImplicitPendingPriorityFwd then
                stashPendingPrio g
              else g
            g.chainPendingReplacement (.receivePriority prio)
        return (g, false)
      else if g.pending != .none || g.afterRandom != .none then
        return (stashPendingPrio g, false)
      else if !g.continuations.isEmpty || g.pendingReplacement.isSome ||
          g.currentInterpWait?.isSome then
        return (g, true)
      else if !g.over && g.triggerNeedingTargets.isSome then
        let g := stashPendingPrio g
        return (if alwaysGrantPriority then g else g.promptTriggerTargetsIfNeeded, false)
      else
        return (g.receivePriority prio, false)
    let g :=
      if g.pending == .none && g.continuations.isEmpty && !followedByFinishChoice &&
          g.priority != prio then
        g.change (.priority prio)
      else g
    if followedByFinishChoice && !g.sbaPaused then
      let g :=
        if g.pending == .none && g.continuations.isEmpty &&
            g.pendingReplacement.isNone && g.outerPendingReplacements.isEmpty &&
            g.currentInterpWait?.isNone && g.pendingPriority.isNone then
          stashPendingPrio g
        else g
      return (g, true)
    else if (resumeContinuation || (doReconcileDep && g.pending == .none && g.afterRandom == .none)) &&
        (!g.continuations.isEmpty || g.pendingReplacement.isSome) then
      return (g, true)
    else if g.pending == .none && g.continuations.isEmpty then
      if alwaysGrantPriority then
        if !g.over && g.triggerNeedingTargets.isSome then
          return (stashPendingPrio g, false)
        else
          return (g.receivePriority prio, false)
      else
        let g :=
          if g.waitingTriggers.size > baseTriggers || hasUnreversedActions then
            g.receivePriority prio
          else g
        let g :=
          if !g.over && g.pending == .none && g.continuations.isEmpty &&
              g.triggerNeedingTargets.isSome then
            (stashPendingPrio g).promptTriggerTargetsIfNeeded
          else g
        return (g, false)
    else
      return (g, false)

@[extern "mtg_game_drain_pending_continuations"]
private opaque drainPendingContinuations (g : Game) : Game := g

@[extern "mtg_game_reverse_proposed_spell"]
private opaque reverseProposedSpell (g : Game) (resumeContinuation : Bool := false)
    (extraLog : Option String := none) (alwaysGrantPriority : Bool := false)
    (skipDepartureReconcile : Bool := false)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Game := g

@[extern "mtg_game_proposal_cost_prompt_still_payable"]
opaque proposalCostPromptStillPayableFwd (g : Game) (caster : PlayerId) (p : Pending) : Bool := false

@[extern "mtg_game_reverse_proposed_spell_except"]
opaque reverseProposedSpellExceptFwd (g : Game) (resumeContinuation : Bool := false)
    (extraLog : Option String := none) (alwaysGrantPriority : Bool := false)
    (skipDepartureReconcile : Bool := false)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) :
    Except String Game := .ok g

@[extern "mtg_game_resume_after_become_cast"]
opaque resumeAfterBecomeCastFwd (g : Game) : Game := g

/-- Clear `.payWard` once a ward cost is paid or declined, draining any active
`pendingReplacement` / `outerPendingReplacements` continuations before finishing
active resolutions, trigger target announcements, or priority (CR 702.21a / 608.2n). -/
partial def afterWardResolved (g : Game) : Game :=
  let reverseOrphanedIfOver (g : Game) : Game :=
    let g :=
      if g.proposedSpell.any (fun prop =>
          !g.stillInGame prop.caster || (g.findObject? prop.spellId).isNone) then
        (if g.pending == .none then g else g.change (.pending .none)).reverseProposedSpell
          (resumeContinuation := true) (alwaysGrantPriority := true)
      else g
    g.completeActiveResolutions
  let replaceTopOuters (g : Game) (popCount : Nat) (nextOuters : Array PendingReplacement) : Game :=
    let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
    let g := (Array.replicate popCount EngineChange.popOuterPendingReplacement).foldl Game.change g
    (nextOuters.map EngineChange.pushOuterPendingReplacement).foldl Game.change g
  let rec finishWardTail (g : Game) : Game :=
    if g.sbaPaused then
      if g.anyContinuationSettlesControlFlowFwd then g
      else g.chainPendingReplacement .afterWardResolved
    else if let .chooseReplacement .. := g.pending then
      if g.anyContinuationSettlesControlFlowFwd then g
      else g.chainPendingReplacement .afterWardResolved
    else if g.pending != .none || g.afterRandom != .none then
      g
    else if g.pendingReplacement.isSome then
      if g.anyContinuationSettlesControlFlowFwd then g
      else g.chainPendingReplacement .afterWardResolved
    else if let some outer := g.outerPendingReplacements.back? then
      let g := g.changes #[.popOuterPendingReplacement, .pendingReplacement (some outer)]
      if g.anyContinuationSettlesControlFlowFwd then g
      else g.chainPendingReplacement .afterWardResolved
    else if !g.over && g.proposedSpell.isNone &&
        (g.pendingMayCastFromExile.isSome || g.pendingFreeCopies.isSome) then
      let g := g.reopenDeferredExileCasts
      if let .chooseReplacement .. := g.pending then
        if g.anyContinuationSettlesControlFlowFwd then g
        else g.chainPendingReplacement .afterWardResolved
      else if g.over || g.pending != .none || g.afterRandom != .none then
        g
      else
        finishWardTail g
    else
      let g := g.completeActiveResolutions
      if g.over then g
      else if let .chooseReplacement .. := g.pending then
        if g.anyContinuationSettlesControlFlowFwd then g
        else g.chainPendingReplacement .afterWardResolved
      else if g.pending != .none || g.afterRandom != .none then g
      else if g.triggerNeedingTargets.isSome then g.promptTriggerTargetsIfNeeded
      else if g.proposedSpell.any (fun prop =>
          !g.stillInGame prop.caster || (g.findObject? prop.spellId).isNone) then
        let g :=
          (if g.pending == .none then g else g.change (.pending .none)).reverseProposedSpell
            (resumeContinuation := true) (alwaysGrantPriority := true)
        if !g.over && g.pending == .none && g.continuations.isEmpty &&
            g.triggerNeedingTargets.isSome then
          g.promptTriggerTargetsIfNeeded
        else g
      else if g.proposedSpell.isSome then g
      else
        let prio := g.pendingPriority.getD g.activePlayer
        g.receivePriority prio
  let g :=
    match g.pending with
    | .payWard .. => g.change (.pending .none)
    | _ => g
  let postPromptSettles (gCur : Game) : Bool :=
    let cs : Array EngineChange :=
      (if !gCur.sbaPaused && gCur.pending != .none then #[EngineChange.pending .none] else #[]) ++
      (if gCur.afterRandom != .none then #[EngineChange.afterRandom .none] else #[])
    (if cs.isEmpty then gCur else gCur.changes cs).anyContinuationSettlesControlFlowFwd
  if g.over then
    reverseOrphanedIfOver g
  else if (g.currentInterpWait?.isSome) &&
      (g.pending != .none || g.afterRandom != .none) then
    if postPromptSettles g then g
    else
      let existing := g.outerPendingReplacements
      replaceTopOuters g existing.size (#[.afterWardResolved] ++ existing)
  else if g.currentInterpWait?.isSome then
    let stashedPending := g.pendingReplacement
    let stashedOuters := g.outerPendingReplacements
    let g := if stashedPending.isSome then g.change (.pendingReplacement none) else g
    let g := (Array.replicate stashedOuters.size EngineChange.popOuterPendingReplacement).foldl Game.change g
    let rec drainTriggerWithDeferredExile (g : Game) : Game :=
      let g := g.drainPendingContinuations
      if !g.over && (g.currentInterpWait?.isSome) &&
          g.pending == .none && g.afterRandom == .none && g.proposedSpell.isNone &&
          (g.pendingMayCastFromExile.isSome || g.pendingFreeCopies.isSome) then
        let g := g.reopenDeferredExileCasts
        if !g.over && g.pending == .none && g.afterRandom == .none then
          drainTriggerWithDeferredExile g
        else g
      else g
    let g := drainTriggerWithDeferredExile g
    if g.over then
      reverseOrphanedIfOver g
    else
      let drainSuffix :=
        if g.pending != .none || g.afterRandom != .none then g.outerPendingReplacements
        else #[]
      if g.currentInterpWait?.isSome then
        let gRestored :=
          match stashedPending with
          | some c => replaceTopOuters g drainSuffix.size ((stashedOuters.push c) ++ drainSuffix)
          | none =>
            if stashedOuters.isEmpty then g
            else replaceTopOuters g drainSuffix.size (stashedOuters ++ drainSuffix)
        if postPromptSettles gRestored then gRestored
        else
          let wardCont :=
            match stashedPending with
            | some c => .seq c .afterWardResolved
            | none => .afterWardResolved
          replaceTopOuters g drainSuffix.size ((stashedOuters.push wardCont) ++ drainSuffix)
      else
        let g :=
          if g.pending != .none || g.afterRandom != .none then
            let wardTail :=
              match stashedPending with
              | some c => stashedOuters.push c
              | none => stashedOuters
            if wardTail.isEmpty then g
            else replaceTopOuters g drainSuffix.size (wardTail ++ drainSuffix)
          else
            let g :=
              match stashedPending with
              | some c => g.chainPendingReplacement c
              | none => g
            if stashedOuters.isEmpty then g
            else replaceTopOuters g drainSuffix.size (stashedOuters ++ drainSuffix)
        finishWardTail g
  else
    finishWardTail g

/-- Whether an active resolution or pending choice was already open before the
current spell or ability proposal began (ignoring any `ContinuationFrame` pushed
solely by `promptChooseReplacement` during mana abilities or multi-step cost
payments, CR 117.3c / 601.2 / 602.2). -/
def proposalHadOpenContinuation (g : Game) (fallback : Option Bool := none) : Bool :=
  match g.proposalCheckpoint with
  | some ckpt => !ckpt.continuations.isEmpty || ckpt.pending != .none
  | none => fallback.getD (!g.continuations.isEmpty)

/-- Run post-cast cleanup, offer any remaining `pendingMayCastFromExile` or
`pendingFreeCopies` casts, and resume active continuations or grant priority
(CR 601.2i / 117.3c). -/
def finishPostCast (g : Game) (p : PlayerId)
    (grantPriority : Bool := true)
    (hadOuterReplacement : Bool := false)
    (hadOpenContinuation : Bool := false) : Game :=
  let g := g.runPostCastCleanup
  -- Doom Reigns Supreme: offer another exiled spell after this cast finishes.
  let g : Game :=
    match g.pendingMayCastFromExile with
    | some (q, ids, left) =>
      if q != p || g.pending != Pending.none then g
      else
        let alive := ids.filter (fun id =>
          (g.findObject? id).any (fun (o : GameObject) =>
            o.zone == Zone.exile && isCastableObject o && !g.isLand o))
        let g := g.change (.pendingMayCastFromExile none)
        if !g.stillInGame q || alive.isEmpty || left == 0 then g
        else
          g.beginResolutionChoice q (.mayCastUpToFromExile alive left)
            s!"{(g.player q).name} may cast up to {left} more spells from among the exiled cards without paying their mana costs"
    | none => g
  -- Uldaros Theorix: offer the remaining copies until none can be cast.
  let g :=
    match g.pendingFreeCopies with
    | some (q, ids, budget, castsLeft) =>
      if q != p || g.pending != .none then g
      else
        let alive := ids.filter (fun id => (g.findObject? id).any (·.zone == .exile))
        let castable := alive.filter (fun id =>
          (g.findObject? id).any (fun o => g.objectManaValue o ≤ budget))
        if !g.stillInGame q || castable.isEmpty || castsLeft == 0 then
          let g :=
            if alive.isEmpty then g
            else
              g.withBatch (some (.stateBased .copyOutsideStackOrBf)) fun g =>
                alive.foldl (fun g id =>
                  g.ceaseToExist id (cause := some (.stateBased .copyOutsideStackOrBf))) g
          g.change (.pendingFreeCopies none)
        else
          (g.change (.pendingFreeCopies none)).beginResolutionChoice q (.castCopiesFree alive budget castsLeft)
    | none => g
  let prio := if hadOpenContinuation then g.activePlayer else p
  if !grantPriority || hadOuterReplacement then g
  else if let .chooseReplacement .. := g.pending then
    if g.anyContinuationSettlesControlFlowFwd then
      if g.hasImplicitPendingPriorityContinuationFwd && g.pendingPriority.isNone then
        g.change (.pendingPriority (some (g.priorityInstead prio)))
      else g
    else if g.currentInterpWait?.isSome then
      let g :=
        if g.pendingPriority.isNone then
          g.change (.pendingPriority (some (g.priorityInstead prio)))
        else g
      g.chainPendingReplacement .finishResolutionChoice
    else
      g.chainPendingReplacement (.receivePriority prio)
  else if g.pending != .none then g
  else if g.currentInterpWait?.isSome || g.pendingReplacement.isSome ||
      !g.outerPendingReplacements.isEmpty then
    if g.anyContinuationSettlesControlFlowFwd then
      if g.hasImplicitPendingPriorityContinuationFwd && g.pendingPriority.isNone then
        g.change (.pendingPriority (some (g.priorityInstead prio)))
      else g
    else
      let g :=
        if g.pendingPriority.isNone then
          g.change (.pendingPriority (some (g.priorityInstead prio)))
        else g
      g.chainPendingReplacement .finishResolutionChoice
  else g.receivePriority prio

def becomeCast (g : Game) (p : PlayerId) (spell : GameObject)
    (grantPriority : Bool := true)
    (hadOuterReplacement : Bool := false)
    (hadOpenContinuation : Option Bool := none) : Game :=
  let openCont := g.proposalHadOpenContinuation hadOpenContinuation
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishBecomeCast p spell.id grantPriority hadOuterReplacement openCont)
  else
    let clearProp := if g.proposedSpell.isSome then #[EngineChange.proposedSpell none] else #[]
    let clearCkpt := if g.proposalCheckpoint.isSome then #[EngineChange.clearProposalCheckpoint] else #[]
    let g := g.changes (clearProp ++ clearCkpt ++ #[EngineChange.castingFromTop false])
    let g := g.logMsg s!"{(g.player p).name} casts {g.name spell}"
    -- Emrakul, the Exigent Doom: the granted mana ability lasts until the card
    -- is cast from exile, so it can help pay for that spell (ruling 729).
    let g := g.battlefield.foldl (fun g land =>
      (g.colorlessGrantUntilCast land).foldl (fun g cid =>
        if g.followMoved cid == spell.id then
          g.expireEffect (.colorlessGrantUntilCast land.id cid)
        else g) g) g
    -- Theorist's Proxy: the next spell this player casts this turn.
    let g :=
      if g.nextSpellCantBeCountered p && !GameEvent.isUncastStackCopy g.events spell.id then
        let g := g.expireEffect (.nextSpellCantBeCounteredThisTurn p)
        (g.createEffect (.uncounterableThisCast spell.id)).logMsg
          s!"{g.name spell} can't be countered"
      else g
    let g := g.putCastTriggersOnStack p spell
    let liveCmds := g.objects.filter (fun o => o.owner == p && o.isCommander)
    let cmdTypes :=
      if !liveCmds.isEmpty then
        liveCmds.foldl (fun acc o => acc ++ (g.subtypes o).filter CardSubtype.isCreatureType) #[]
      else
        (g.player p).commanderCreatureTypes
    let g :=
      if g.pending == .none && g.isCreature spell &&
          g.ancestryManaSpentOn spell.id &&
          (g.subtypes spell).any (fun sub => sub.isCreatureType && cmdTypes.contains sub) then
        g.beginScry p 1
      else g
    if let .scry .. := g.pending then
      let needsDeferredPostCast :=
        g.postCastCleanup.isSome || g.pendingMayCastFromExile.isSome ||
          g.pendingFreeCopies.isSome ||
          g.currentInterpWait?.isSome || g.pendingReplacement.isSome ||
          hadOuterReplacement || !grantPriority ||
          (grantPriority && !openCont && p != g.activePlayer)
      if needsDeferredPostCast then
        let existingOuter? := g.pendingReplacement
        let g := if existingOuter?.isSome then g.change (.pendingReplacement none) else g
        let g := g.chainPendingReplacement
          (.finishPostCast p grantPriority (hadOuterReplacement || existingOuter?.isSome) openCont)
        match existingOuter? with
        | some outer =>
          g.chainProposalOuterCont p outer (grantPriority := grantPriority)
            (hadOuterReplacement := hadOuterReplacement) (openCont := openCont)
        | none => g
      else g
    else
      g.finishPostCast p grantPriority hadOuterReplacement openCont

/-- After targets are announced, reduce the locked-in cost if the spell cares
about a damaged, tapped, or attacking nontoken target, or the ability about
its target's power, counters, or equip discounts (CR 601.2f). -/
def lockInTargetCostReduction (g : Game) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop =>
    match g.findObject? prop.spellId with
    | none => g
    | some spell =>
      let face := g.baseCard spell
      match (g.stackEntry? spell.id).bind (fun e => e.targets[0]?) with
      | some (Target.permanent oid) =>
        match g.findObject? oid with
        | some o =>
          let isSpell := prop.kind == .spell
          let targets := ((g.stackEntry? spell.id).map (·.targets)).getD #[]
          let nSpellTarget : Nat :=
            if !isSpell then 0
            else
              let tcs := g.evalLayer3 spell
              let faceStatics :=
                if tcs.isEmpty then face.staticAbilities
                else HasTextChange.applyTextChanges tcs face.staticAbilities
              let spellEnv : EvalEnv :=
                { controller := prop.caster
                  sourceId := some spell.id
                  targetSlots := targets.map (fun t => #[t])
                  chosenX := spell.chosenX.getD 0 }
              faceStatics.foldl (fun acc ab =>
                match ab with
                | .costModifier cond? .thisSpell (.reduceGeneric amt) =>
                  if (cond?.any Condition.mentionsTarget || amt.mentionsTarget) &&
                      cond?.all (EvalExpr.evalCondition g spellEnv) then
                    acc + (EvalExpr.evalValue g spellEnv amt).toNat
                  else acc
                | _ => acc) 0
          let nActTarget :=
            match prop.activation with
            | some ab =>
              let targetReds := ab.costReductions.filter (·.mentionsTarget)
              if targetReds.isEmpty then 0
              else EvalExpr.evalActivationCostReductions g prop.caster prop.sourceId targetReds targets
            | none => 0
          let nEquip : Nat :=
            match prop.activation with
            | none => 0
            | some ab =>
              let oEnv : EvalEnv := { controller := (g.controllerOf o).getD o.owner, sourceId := some o.id }
              (g.staticAbilities o).foldl (fun acc sab =>
                match sab with
                | .costModifier cond? (.abilities act tag? sc (some tgtPred) none) (.reduceGeneric amt) =>
                  let tagOk := match tag? with
                    | none => true
                    | some t => ab.tag? == some t || (match t with | .equip _ => ab.isEquip | _ => false)
                  let srcOk := match prop.sourceId.bind g.findObject? with
                    | some src => EvalExpr.evalObjectPred g oEnv (.live src) sc.pred
                    | none => true
                  if tagOk && srcOk &&
                      EvalExpr.matchesPlayerFilter g oEnv act prop.caster &&
                      cond?.all (EvalExpr.evalCondition g oEnv) &&
                      EvalExpr.evalObjectPred g oEnv (.live o) tgtPred then
                    acc + (EvalExpr.evalValue g oEnv amt).toNat
                  else acc
                | _ => acc) 0
          let n := nSpellTarget + nActTarget + nEquip
          if n == 0 then g
          else g.changeProposal (.reduceCostBy (ManaCost.ofGeneric n))
        | none => g
      | _ => g

/-- Finish the post-loyalty steps (`clearProposalCheckpoint`, `abilityActivated`,
and priority / continuation resumption) of `becomeActivated`. -/
def finishPostLoyaltyActivated (g : Game) (p : PlayerId) (sourceName : String)
    (sourceId : Option ObjectId := none) (activation : Option ActivatedAbility := none)
    (abilityId : Option ObjectId := none)
    (sourceSnap : Option EventObject := none)
    (srcObj? : Option GameObject := none)
    (hadOuterReplacement : Bool := false)
    (openCont : Bool := false)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Game :=
  let prio := if openCont then g.activePlayer else p
  if g.over || !g.stillInGame p ||
      !abilityId.all (fun aid =>
        sourceId == some aid || (g.findObject? aid).any (·.zone == .stack)) then
    if g.proposedSpell.isSome && g.proposalCheckpoint.isSome then
      g.reverseProposedSpell (resumeContinuation := true)
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?)
    else
      let clearProp := if g.proposedSpell.isSome then #[EngineChange.proposedSpell none] else #[]
      let clearCkpt := if g.proposalCheckpoint.isSome then #[EngineChange.clearProposalCheckpoint] else #[]
      let g := g.changes (clearProp ++ clearCkpt)
      if !g.over && !hadOuterReplacement && g.pending == .none then
        if g.pendingReplacement.isSome || !g.outerPendingReplacements.isEmpty ||
            g.currentInterpWait?.isSome then
          g.chainFinishChoicePreservingPriority prio
        else
          g.receivePriority (g.priorityInstead prio)
      else g
  else
    let chosenX :=
      ((abilityId.bind g.findObject?).bind (·.chosenX)).getD 0
    let isEquip := activation.any (·.isEquip)
    let source : EventObject :=
      match (sourceId.bind g.findObject?).map g.snapshot <|> sourceSnap with
      | some src => src
      | none =>
        if isEquip then
          { id := sourceId, name := sourceName, controller := some p, owner := p,
            types := #[.artifact], subtypes := #[.equipment] }
        else
          { id := sourceId, name := sourceName, controller := some p, owner := p }
    let abilityObjId := abilityId.orElse (fun _ => sourceId) |>.getD noSourceSentinelId
    let loyaltyDelta : Option Int :=
      activation.bind (·.cost.netLoyaltyDelta chosenX)
    let isPowerUp : Bool :=
      match activation with
      | some ab => ab.isPowerUp
      | none => srcObj?.any (fun src => (g.baseCard src).activatedAbilities.any (·.isPowerUp))
    let isBoast :=
      activation.any (fun ab => ab.isBoast || ab.cost.exileManaSymbols?.isSome)
    let abilityIdx : Option Nat :=
      (g.proposedSpell.bind (·.abilityIdx)).orElse fun _ =>
        match srcObj?, activation with
        | some src, some ab => (g.activatedAbilitiesOf src).findIdx? (· == ab)
        | _, _ => none
    let isExhaust : Bool := activation.any (·.isExhaust)
    let clearProp := if g.proposedSpell.isSome then #[EngineChange.proposedSpell none] else #[]
    let clearCkpt := if g.proposalCheckpoint.isSome then #[EngineChange.clearProposalCheckpoint] else #[]
    let g := g.changes (clearProp ++ clearCkpt)
    let g := g.record (GameEvent.abilityActivated g.turnNumber abilityObjId source p
      (.nonMana loyaltyDelta isEquip isPowerUp isBoast abilityIdx isExhaust))
    let g := g.logMsg s!"{(g.player p).name} activates {sourceName}"
    if g.pending != .none then g
    else if hadOuterReplacement then
      g
    else if g.currentInterpWait?.isSome || g.pendingReplacement.isSome ||
        !g.outerPendingReplacements.isEmpty then
      g.chainFinishChoicePreservingPriority prio
    else g.receivePriority prio

/-- Finish turning a face-down permanent face up once all morph/megamorph/disguise
costs have been paid, deferring `GameEvent.turnedFaceUp`, clearing proposal state,
and granting priority across `Pending.chooseReplacement` (CR 116.2b / 708.8). -/
def completeTurnFaceUp (g : Game) (caster : PlayerId) (spellId : ObjectId)
    (hadOuterReplacement : Bool := false)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Game × Bool :=
  if g.over || !g.stillInGame caster then
    if !g.over && g.proposedSpell.isSome && g.proposalCheckpoint.isSome then
      (g.reverseProposedSpell (resumeContinuation := true)
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?), false)
    else if g.over then
      (g, false)
    else
      let clearPending : Array EngineChange :=
        if isProposalPromptFor caster g.pending then #[.pending .none] else #[]
      let clearProp : Array EngineChange :=
        if g.proposedSpell.isSome then #[.proposedSpell none] else #[]
      let clearCkpt : Array EngineChange :=
        if g.proposalCheckpoint.isSome then #[.clearProposalCheckpoint] else #[]
      let changes := clearPending ++ clearProp ++ clearCkpt
      let g := if changes.isEmpty then g else g.changes changes
      if g.over || g.pending != .none then (g, false)
      else if !hadOuterReplacement && (g.pendingReplacement.isSome ||
          !g.outerPendingReplacements.isEmpty || g.currentInterpWait?.isSome) then
        let g := g.chainFinishChoicePreservingPriority caster
        if !g.over && g.pending == .none && g.pendingReplacement.isNone then
          (g.drainPendingContinuations, false)
        else (g, true)
      else if !hadOuterReplacement && g.continuations.isEmpty then
        (g.receivePriority (g.priorityInstead caster), false)
      else
        (g, !g.over && g.pending == .none)
  else if let .chooseReplacement .. := g.pending then
    (g.chainPendingReplacement (.finishTurnFaceUp caster spellId hadOuterReplacement), false)
  else
    match (g.findObject? spellId).filter (fun o =>
        o.isOnBattlefield && o.status.faceDown && g.controlledBy o caster) with
    | none =>
      if g.proposedSpell.isSome && g.proposalCheckpoint.isSome then
        (g.reverseProposedSpell (resumeContinuation := true)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?), false)
      else
        let wasIdle := g.pending == .none || isProposalPromptFor caster g.pending
        let clearPending : Array EngineChange :=
          if isProposalPromptFor caster g.pending then #[.pending .none] else #[]
        let clearCkpt : Array EngineChange :=
          if g.proposalCheckpoint.isSome then #[.clearProposalCheckpoint] else #[]
        let g := g.changes (clearPending ++ #[.proposedSpell none, .consecutivePasses 0] ++ clearCkpt)
        if !g.over && !hadOuterReplacement && wasIdle && g.pending == .none &&
            g.continuations.isEmpty && g.pendingReplacement.isNone &&
            g.outerPendingReplacements.isEmpty && g.currentInterpWait?.isNone then
          (g.receivePriority (g.priorityInstead caster), false)
        else if !g.over && !hadOuterReplacement && g.pending == .none &&
            (g.pendingReplacement.isSome || !g.outerPendingReplacements.isEmpty ||
              g.currentInterpWait?.isSome) then
          let g := g.chainFinishChoicePreservingPriority caster
          if !g.over && g.pending == .none && g.pendingReplacement.isNone then
            (g.drainPendingContinuations, false)
          else (g, !g.over && g.pending == .none)
        else
          (g, !g.over && g.pending == .none)
    | some o =>
      let clearPending : Array EngineChange :=
        if isProposalPromptFor caster g.pending then #[.pending .none] else #[]
      let clearCkpt : Array EngineChange :=
        if g.proposalCheckpoint.isSome then #[.clearProposalCheckpoint] else #[]
      let g := g.changes (clearPending ++ #[.proposedSpell none, .consecutivePasses 0] ++ clearCkpt)
      let pre := g
      let g := g.record
        (GameEvent.turnedFaceUp g.turnNumber (g.snapshot o)
          (cause := .specialAction .turnFaceUp caster))
      let objName := (g.findObject? spellId).map g.name |>.getD (g.name o)
      let g := g.logMsg s!"{(g.player caster).name} turns {objName} face up"
      let hadPreReconcileCont :=
        g.currentInterpWait?.isSome || g.pendingReplacement.isSome || !g.outerPendingReplacements.isEmpty
      let g :=
        (reconcileControlAfterTransition pre g (cause := some (.specialAction .turnFaceUp caster)))
          |>.flushQueuedLinkedExile
      let skipTail := g.over || hadOuterReplacement
      let chainFinishChoice := !skipTail && hadPreReconcileCont
      let g :=
        if skipTail then g
        else if chainFinishChoice then
          g.chainFinishChoicePreservingPriority caster
        else
          let g :=
            if !g.sbaPaused && g.pending != .none && g.pendingPriority.isNone then
              match g.pending with
              | .chooseReplacement .. => g
              | _ => g.change (.pendingPriority (some (g.priorityInstead caster)))
            else g
          g.receivePriority caster
      if hadOuterReplacement then (g, !g.over && g.pending == .none)
      else if !g.over && g.pending == .none then (g.drainPendingContinuations, false)
      else (g, false)

def becomeActivated (g : Game) (p : PlayerId) (sourceName : String)
    (sourceId : Option ObjectId := none) (activation : Option ActivatedAbility := none)
    (abilityId : Option ObjectId := none)
    (sourceSnapshot : Option EventObject := none)
    (sourceOriginal : Option GameObject := none)
    (hadOuterReplacement : Bool := false)
    (hadOpenContinuation : Option Bool := none)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Game :=
  let openCont := g.proposalHadOpenContinuation hadOpenContinuation
  let activation := activation <|> g.proposedSpell.bind (·.activation)
  let abilityId := abilityId <|> g.proposedSpell.map (·.spellId) <|> g.stack.back?.map (·.objectId)
  let sourceSnap :=
    (sourceId.bind g.findObject?).map g.snapshot <|> sourceSnapshot <|>
      g.proposedSpell.map (·.originalSnapshot)
  let srcObj? : Option GameObject :=
    (sourceId.bind g.findObject?) <|> sourceOriginal <|> g.proposedSpell.map (·.original)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishBecomeActivated p sourceName sourceId activation
      abilityId sourceSnap srcObj? hadOuterReplacement openCont)
  else
    let chosenX :=
      ((abilityId.bind g.findObject?).bind (·.chosenX)).getD 0
    let sinceIdx := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD 0
    let unpaidLoyaltyUnpayable : Bool :=
      match activation.bind (·.cost.netLoyaltyDelta chosenX) with
      | none => false
      | some k =>
        if g.proposedSpell.any ProposedSpell.loyaltyPaid ||
            sourceId.any (fun sid =>
              g.sourceCounterCostPaidFor sid abilityId .loyalty (some .loyalty) sinceIdx) then
          false
        else
          match sourceId.bind g.findObject? with
          | none => true
          | some src =>
            !src.isOnBattlefield || !g.controlledBy src p ||
              g.loyaltyActivatedThisTurn src.id ||
              (k < 0 && (src.status.loyaltyCounters : Int) < -k)
    if unpaidLoyaltyUnpayable then
      if g.proposedSpell.isSome && g.proposalCheckpoint.isSome then
        g.reverseProposedSpell (resumeContinuation := true)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?)
      else
        let clearProp := if g.proposedSpell.isSome then #[EngineChange.proposedSpell none] else #[]
        let clearCkpt := if g.proposalCheckpoint.isSome then #[EngineChange.clearProposalCheckpoint] else #[]
        let g := g.changes (clearProp ++ clearCkpt)
        let prio := if openCont then g.activePlayer else p
        if !g.over && !hadOuterReplacement && g.pending == .none then
          if g.pendingReplacement.isSome || !g.outerPendingReplacements.isEmpty ||
              g.currentInterpWait?.isSome then
            g.chainFinishChoicePreservingPriority prio
          else
            g.receivePriority (g.priorityInstead prio)
        else g
    else
      let localOuter? := g.pendingReplacement
      let hadOuter := hadOuterReplacement || localOuter?.isSome
      let g := if localOuter?.isSome then g.change (.pendingReplacement none) else g
      let g :=
        match activation.bind (·.cost.netLoyaltyDelta chosenX) with
        | some k =>
          match sourceId.bind g.findObject? with
          | some src =>
            if !(g.proposedSpell.any ProposedSpell.loyaltyPaid) &&
                !g.sourceCounterCostPaidFor src.id abilityId .loyalty (some .loyalty) sinceIdx then
              g.payLoyaltyDelta p src k (forObject := abilityId)
            else g
          | none => g
        | none => g
      if let .chooseReplacement .. := g.pending then
        let g := g.chainPendingReplacement (.finishPostLoyaltyActivated p sourceName sourceId
          activation abilityId sourceSnap srcObj? hadOuter openCont)
        match localOuter? with
        | some outer =>
          g.chainProposalOuterCont p outer (hadOuterReplacement := hadOuterReplacement)
            (openCont := openCont)
        | none => g
      else
        let g :=
          match localOuter? with
          | some outer =>
            g.chainProposalOuterCont p outer (hadOuterReplacement := hadOuterReplacement)
              (openCont := openCont)
          | none => g
        g.finishPostLoyaltyActivated p sourceName sourceId activation abilityId sourceSnap
          srcObj? hadOuter openCont
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?)

/-- Finish paying the proposed activation once its mana is paid and every
chosen cost is paid: tap, life, and the source's own costs, then put it on
the stack (CR 601.2h–i / 602.2b). -/
def completeActivation (g : Game) (prop : ProposedSpell)
    (hadOuterReplacement : Bool := false)
    (hadOpenContinuation : Option Bool := none)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Except String Game := do
  let openCont := g.proposalHadOpenContinuation hadOpenContinuation
  if let .chooseReplacement .. := g.pending then
    return (g.change (.consecutivePasses 0)).chainPendingReplacement
      (.completeActivation hadOuterReplacement openCont)
  let some sid := prop.sourceId | throw "The ability has no source"
  let x := ((g.findObject? prop.spellId).bind (·.chosenX)).getD 0
  let srcSnap := (g.findObject? sid).map g.snapshot |>.orElse (fun _ => some prop.originalSnapshot)
  let fallbackName :=
    if prop.originalSnapshot.name.isEmpty then g.name prop.original
    else prop.originalSnapshot.name
  let srcName := (g.findObject? sid).map g.name |>.getD fallbackName
  let localOuter? := g.pendingReplacement
  let hadOuter := hadOuterReplacement || localOuter?.isSome
  let g0 := if localOuter?.isSome then g.change (.pendingReplacement none) else g
  let g ← g0.payActivationExtraCosts prop.caster sid prop.tapSource prop.sacrificeSource
    prop.payLife prop.discardSource prop.activation (if prop.removePlusOneX then x else 0)
    (callerOuter? := localOuter?)
    (followedByFinishChoice := followedByFinishChoice)
    (followedByExplicitPriority? := followedByExplicitPriority?)
  if g.proposedSpell.isNone then
    return g
  if prop.needsSacrificeOther then
    let prompt := s!"{(g.player prop.caster).name} must sacrifice another creature or artifact"
    if let .chooseReplacement .. := g.pending then
      let g := (g.change (.consecutivePasses 0)).chainPendingReplacement
        (.restorePending (.sacrificePermanent prop.caster sid) (promptLog := some prompt))
      return match localOuter? with
        | some outer => g.chainPendingReplacement outer
        | none => g
    else
      if (g.sacrificeCreatureOrArtifactChoices prop.caster sid).isEmpty then
        throw "No creature or artifact to sacrifice"
      let g :=
        match localOuter? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      let g := g.changes #[.pending (.sacrificePermanent prop.caster sid), .consecutivePasses 0]
      return g.logMsg prompt
  let paused := match g.pending with | .chooseReplacement .. => true | _ => false
  let g :=
    if !paused then
      match localOuter? with
      | some outer =>
        g.chainProposalOuterCont prop.caster outer (hadOuterReplacement := hadOuterReplacement)
          (openCont := openCont)
      | none => g
    else g
  let clearPending : Array EngineChange :=
    if paused then #[] else #[.pending .none]
  let g := g.changes (clearPending ++ #[.consecutivePasses 0])
  let g := g.becomeActivated prop.caster srcName prop.sourceId prop.activation
    (abilityId := some prop.spellId)
    (sourceSnapshot := srcSnap)
    (sourceOriginal := some prop.original)
    (hadOuterReplacement := hadOuter)
    (hadOpenContinuation := some openCont)
    (followedByFinishChoice := followedByFinishChoice)
    (followedByExplicitPriority? := followedByExplicitPriority?)
  let g :=
    if paused then
      match localOuter? with
      | some outer =>
        g.chainProposalOuterCont prop.caster outer (hadOuterReplacement := hadOuterReplacement)
          (openCont := openCont)
      | none => g
    else g
  return g

/-- Whether the proposed spell or ability still needs targets announced (CR 601.2c). -/
def proposedNeedsTarget (g : Game) (prop : ProposedSpell) : Bool :=
  match g.findObject? prop.spellId with
  | none => false
  | some o =>
    match prop.kind with
    | .spell =>
      match g.currentSpellEffect o with
      | some e => e.requiresTarget
      | none =>
        let bc := g.baseCard o
        if isModalSpellFace bc then false
        else bc.requiresTarget || g.isAura o
    | .activatedAbility =>
      match o.abilityEffect with
      | some e => e.requiresTarget
      | none => false
    | .turnFaceUp => false

/-- Choose new targets for a spell on the stack (Speedball; MSH 370).
Each slot that has no new legal target is left unchanged, even if the
current target is illegal. -/
def retargetStackSpell (g : Game) (spellId : ObjectId) (newTargets : Array Target) :
    Game :=
  match g.stack.findIdx? (fun e => e.objectId == spellId) with
  | none => g.logMsg "The spell is no longer on the stack"
  | some i =>
    let e := g.stack[i]!
    match g.findObject? spellId with
    | none => g.logMsg "The spell is no longer on the stack"
    | some spell =>
      let spec := g.targetSpecOf spell
      let merged :=
        if newTargets.size == e.targets.size &&
            g.validTargetArrayForEntry e spell spec newTargets (allowUnchangedIllegal := true) then
          newTargets
        else
          Id.run do
            let selfSource := spell.sourceId.orElse (fun _ => if spell.zone == .stack then some spell.id else none)
            let selfStackId := if spell.zone == .stack then some spell.id else none
            let totalPos := e.targets.size + e.skippedOptionalSlots.size
            let posIndices : Array Nat :=
              if e.skippedOptionalSlots.isEmpty then (List.range e.targets.size).toArray
              else ((List.range totalPos).filter (fun s => !e.skippedOptionalSlots.contains s)).toArray
            let mut staged := e.targets
            for j in [0:Nat.min staged.size newTargets.size] do
              let candT := newTargets[j]!
              let actualPos := posIndices[j]?.getD j
              if candT == e.targets[j]! ||
                  (g.legalTargetsForSlot e.controller (spec.slotAtPos actualPos) selfSource selfStackId).contains candT then
                staged := staged.set! j candT
            if staged != e.targets &&
                g.validTargetArrayForEntry e spell spec staged (allowUnchangedIllegal := true) then
              return staged
            let mut out := e.targets
            for j in [0:Nat.min out.size newTargets.size] do
              let cand := out.set! j newTargets[j]!
              if g.validTargetArrayForEntry e spell spec cand (allowUnchangedIllegal := true) then
                out := cand
            return out
      (g.record (GameEvent.targeted g.turnNumber spellId merged (division := e.dividedDamage)
        (skippedOptionalSlots := e.skippedOptionalSlots))).logMsg
        "New targets are chosen for the spell"

/-- Write `targets` (and optional damage division) onto the stack entry. -/
def setStackEntryTargets (g : Game) (objectId : ObjectId) (targets : Array Target)
    (dividedDamage : Array Nat := #[]) : Game :=
  let skipped := (g.stackEntry? objectId).map (·.skippedOptionalSlots) |>.getD #[]
  g.record (GameEvent.targeted g.turnNumber objectId targets
    (division := dividedDamage) (skippedOptionalSlots := skipped))

/-- How many modes `p` may choose for `face` (CR 700.2): two for “choose one
or both”, “choose up to two”, and “choose two if you control a [subtype]”
while they do. -/
def maxModesFor (g : Game) (p : PlayerId) (face : CardDef) : Nat :=
  if isReturnUpToTwoGyModal face then 2
  else
    match face.modalSpec? with
    | none => 1
    | some ms =>
      let env : EvalEnv := { controller := p, sourceId := g.proposedSpell.map (·.spellId) }
      match ms.altCountIf? with
      | some (cond, _, altMax) =>
        if EvalExpr.evalCondition g env cond then (EvalExpr.evalValue g env altMax).toNat
        else (EvalExpr.evalValue g env ms.maxModes).toNat
      | none => (EvalExpr.evalValue g env ms.maxModes).toNat

/-- Minimum number of modes required for `face` (CR 700.2b): `0` for “choose
up to two”, `1` otherwise. -/
def minModesFor (face : CardDef) : Nat :=
  if isReturnUpToTwoGyModal face then 0
  else
    match face.modalSpec? with
    | some ms => (ms.minModes.evalConst?.getD 1).toNat
    | none => 1

/-- Add `mode` to the proposed spell's chosen modes. -/
def addProposedExtraMode (g : Game) (mode : Nat) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop =>
    let prev :=
      match g.stackEntry? prop.spellId with
      | some se => se.chosenMode.toArray ++ se.extraModes
      | none => #[]
    g.record (GameEvent.announced g.turnNumber prop.spellId (modes := prev.push mode))

/-- Record the chosen mode on the proposed spell's stack entry (CR 700.2). -/
def setProposedMode (g : Game) (mode : Nat) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop =>
    g.record (GameEvent.announced g.turnNumber prop.spellId (modes := #[mode]))


end Game
end Mtg.Engine
