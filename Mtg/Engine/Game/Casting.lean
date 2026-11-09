import Mtg.Engine.Game.Costs

/-!
# Casting legality and payment (CR 601)

Cast timing (flash, sorcery speed), castability from each zone,
restrictions on proposed spells, choosing mana sources for a proposal,
paying costs, reversing an illegal proposal (CR 733.1), ward
(CR 702.21), locking in targets, and becoming cast or activated.
-/

namespace Mtg.Engine
namespace Game

/-- Captain Mar-Vell: as though spells had flash while an opponent has
cast a spell this turn (MSH 105). The permanent need not have been on
the battlefield when that spell was cast. -/
def cosmicAwarenessFlash (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o =>
    (g.staticAbilities o).any (fun
      | .flashIfOpponentCastThisTurn => true
      | _ => false)) &&
    g.players.any (fun q => q.id != p && !g.areTeammates p q.id && g.loggedSpellsCast q.id > 0)

/-- Timing check shared by beginning to cast a spell or an Adventure (CR 601.3)
and CR 601.2b Morph vs. printed-face selection (`excludeStackId := some prop.spellId`). -/
def timingAllowsCast (g : Game) (p : PlayerId) (face : CardDef)
    (excludeStackId : Option ObjectId := none) : Bool :=
  let hasConditionalFlash :=
    match face.flashIfYouControlSubtype with
    | some t => g.controlsAnySubtype p #[t]
    | none => false
  let radagastFlash :=
    face.isCreature && g.loggedCreatureSpells p == 0 &&
      (g.permanentsOf p).any (fun o =>
        (g.baseCard o).firstCreatureHasFlash && g.retainsPrintedAbilities o)
  let prioOk :=
    match excludeStackId with
    | some _ => !g.over && g.priority == p && g.playersReceivePriority
    | none => g.hasPriority p
  let sorceryOk :=
    match excludeStackId with
    | some sid =>
      !g.over && !(g.stack.any (·.objectId != sid)) &&
        g.step.isMainPhase && g.activePlayer == p && g.priority == p
    | none => g.asSorcery? p
  prioOk &&
  (if face.hasSorcerySpeed && !hasConditionalFlash && !radagastFlash &&
      !g.cosmicAwarenessFlash p then
    sorceryOk else true)

/-- Every card face the game knows: each object's card, its other face,
Adventure, and prepare spell, and each sideboard card. A prepare spell's name
is judged by its own characteristics (ruling 745). -/
def knownCardFaces (g : Game) : Array CardDef :=
  let faces (c : CardDef) : Array CardDef :=
    #[c] ++ c.otherFace.toArray ++ (c.adventure.map (·.toCardDef)).toArray ++
      (c.prepareFace.map (·.toCardDef)).toArray
  let fromObjects := g.objects.foldl (fun acc o => acc ++ faces o.printed) #[]
  g.players.foldl (fun acc pl => pl.sideboard.foldl (fun acc c => acc ++ faces c) acc) fromObjects

/-- Whether `name` is the name of a nonland card (CR 201.4a). -/
def isNonlandCardName (g : Game) (name : String) : Bool :=
  g.knownCardFaces.any (fun c => c.name == name && !c.isLand)

/-- Whether a permanent forbids casting spells named `name` (Meddling Mage). -/
def spellNameForbidden (g : Game) (name : String) : Bool :=
  g.battlefield.any (fun o =>
    o.status.chosenName == some name &&
      (g.staticAbilities o).any (· == .fra .chosenNameSpellsCantBeCast))

/-- Whether any living member of the active team controls a permanent forbidding
opponents from casting spells during that player's turn (CR 101.2 / 805.4a / 810.2). -/
def opponentsCantCastOnActiveTurn (g : Game) (p : PlayerId) : Bool :=
  !g.isOnActiveTeam p &&
    (g.teamMembers g.activePlayer).any (fun tm =>
      g.stillInGame tm &&
        (g.permanentsOf tm).any (fun o =>
          (g.staticAbilities o).any (· == .opponentsCantCastOnYourTurn)))

/-- Whether `p`'s graveyard has enough other cards to cast `face` (Ruling 852). -/
def graveyardCastThresholdMet (g : Game) (p : PlayerId) (cardId : ObjectId) (face : CardDef) : Bool :=
  match face.castOnlyIfGraveyardAtLeast with
  | some n => ((g.player p).graveyard.filter (· != cardId)).size >= n
  | none => true

/-- Why a mandatory sacrifice additional cost of `face` cannot be paid, if it cannot
(CR 601.2b / 601.2h / 601.3). -/
def mandatorySacrificeError? (g : Game) (p : PlayerId) (checkId : ObjectId)
    (face : CardDef) (displayName : String := face.name) : Option String :=
  if face.additionalCostSacrificeArtifactOrCreature &&
      face.additionalCostOrPayGeneric.isNone &&
      !(g.permanentsOf p).any (fun perm =>
        perm.id != checkId &&
          if face.additionalCostSacrificeCreatureOrPlaneswalker then
            g.isCreature perm || g.isPlaneswalker perm
          else if face.additionalCostSacrificeCreature then g.isCreature perm
          else g.isCreature perm || g.isArtifact perm) then
    some s!"{displayName} requires sacrificing an artifact or creature"
  else if face.additionalCostSacrificeCreature &&
      !(g.creaturesControlledBy p).any (·.id != checkId) then
    some s!"{displayName} requires sacrificing a creature"
  else none

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
  { name := "", types := #[.creature], power := some 2, toughness := some 2,
    manaCost := ManaCost.ofGeneric 3 }

/-- Whether `p` may begin to cast `o` face down via Morph (CR 702.37a,c / 708.2). -/
def canCastMorphFaceDown (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  let bc := { g.baseCard o with keywords := g.currentKeywords o }
  let fromGraveyard := o.zone == .graveyard o.owner
  let origPerm := g.playPermission o
  let altPerm := origPerm.any (fun pm => pm.withoutManaCost || pm.payLifeEqualManaValue)
  bc.morph.isSome && !fromGraveyard && !altPerm &&
    (origPerm.bind (·.prepareSource)).isNone &&
    !g.splitSecondOnStack && !g.combatLocksNonManaAbilities &&
    !g.opponentsCantCastOnActiveTurn p && !g.spellNameForbidden "" &&
    !g.cantCastSpellsThisTurn p &&
    g.mayPlay p o &&
    (match origPerm with
     | some perm => perm.ignoreTiming || g.timingAllowsCast p morphSpellFace
     | none => g.timingAllowsCast p morphSpellFace)

/-- Whether `p` may begin to cast `o` using its front-face characteristics (CR 601.3). -/
def canCastFrontFace (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  let bc := { g.baseCard o with keywords := g.currentKeywords o }
  let fromGraveyard := o.zone == .graveyard o.owner
  let hadFlashbackPerm := fromGraveyard && g.flashbackUntilEot o
  let isFlashbackCast := fromGraveyard && (bc.flashback.isSome || hadFlashbackPerm)
  !g.isLand o && !g.splitSecondOnStack && !g.combatLocksNonManaAbilities &&
  !g.opponentsCantCastOnActiveTurn p && !g.spellNameForbidden (g.name o) &&
  !g.cantCastSpellsThisTurn p &&
  (o.zone != .library p || g.isCreature o) &&
  g.mayPlay p o &&
  g.graveyardCastThresholdMet p o.id bc &&
  (match g.playPermission o with
   | some perm =>
     (perm.ignoreTiming || g.timingAllowsCast p bc) &&
       (!perm.payLifeEqualManaValue || g.canPayLife p (g.objectManaValue o))
   | none => g.timingAllowsCast p bc) &&
  (g.mandatorySacrificeError? p o.id bc).isNone &&
  (!(isFlashbackCast && bc.flashbackDiscard) || (g.player p).hand.any (· != o.id)) &&
  -- Untargeted permanents, and untargeted instants/sorceries with a modeled
  -- effect (e.g. Night's Whisper), may be proposed (CR 601.3).
  if isModalSpellFace bc then
    let tcs := g.evalLayer3 o
    (effectiveSpellModes bc).any (fun e =>
      let m := if tcs.isEmpty then e else TextChange.applyEffect tcs e
      g.spellModeIsChoosable p m (some o.id)) ||
      isReturnUpToTwoGyModal bc || bc.allowsZeroTargets
  else if bc.requiresTarget then
    -- CR 601.2b–c / 702.33d,g: a target-replacing kicker may be chosen, so legal kicked
    -- targets (Galadriel's Dismissal's player) suffice when no unkicked target is legal.
    bc.allowsZeroTargets || g.castFaceHasLegalTarget p bc (g.evalLayer3 o) (some o.id)
  else bc.isPermanentCard || bc.spellEffect.isSome || isModalSpellFace bc

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
    (explicitAltCost : Bool := false) (flashback : Option Bool := none) : Bool :=
  let bc := g.baseCard o
  -- CR 106.6: the same spending restrictions as `proposedAllowances` for this spell —
  -- Elf, instant/sorcery, Hero, Villain, and artifact-spell mana may pay; creature-source
  -- mana pays only activated abilities, never a spell (MSH 75).
  let allowElf := g.hasSubtype o .elf
  let allowInst := g.isInstantOrSorcery o
  let allowHero := g.hasSubtype o .hero
  let allowVillain := g.hasSubtype o .villain
  let allowCantNonartifact := g.isArtifact o
  let spend : ManaSpend :=
    { spell := true, fromHand := o.zone == .hand p
      supertypes := g.supertypes o, types := g.types o, subtypes := g.subtypes o }
  let canPay (cost : ManaCost) : Bool :=
    available.canPay cost (allowElfRestricted := allowElf) (allowInstRestricted := allowInst)
      (allowHeroRestricted := allowHero) (allowVillainRestricted := allowVillain)
      (allowCantNonartifact := allowCantNonartifact) (allowCreatureRestricted := false)
      (spend := spend)
  let payExtra (n : Nat) : Bool :=
    canPay (g.playManaCost { o with controller := some p } bc (ManaCost.ofGeneric n)
      (origPerm := origPerm) (flashback := flashback) (explicitAltCost := explicitAltCost))
  match bc.additionalCostBeholdOrPay with
  | some (quality, n) =>
    let hasPerm := (g.permanentsOf p).any (fun perm => g.hasSubtype perm quality)
    let hasHand :=
      (g.player p).hand.any (fun id =>
        match g.findObject? id with
        | some card => g.hasSubtype card quality
        | none => false)
    hasPerm || hasHand || payExtra n
  | none =>
  match bc.additionalCostOrPayGeneric, bc.additionalCostDiscardOrPayGeneric with
  | some n, _ =>
    (g.permanentsOf p).any (fun perm =>
      perm.id != o.id &&
        if bc.additionalCostSacrificeCreatureOrPlaneswalker then
          g.isCreature perm || g.isPlaneswalker perm
        else g.isCreature perm || g.isArtifact perm) || payExtra n
  | none, some n =>
    (g.player p).hand.any (fun id => id != o.id) || payExtra n
  | none, none => true

/-- True when the CR 715.3d exile permission forbids recasting as an Adventure. -/
def adventureExileForbidsRecast (g : Game) (o : GameObject) : Bool :=
  match g.playPermission o with
  | some perm => perm.fromAdventure
  | none => false

/-- Validate front-face timing, prohibitions, targets, and mandatory additional
costs when casting `card` as `face` (either upfront in `castSpell` or when
choosing the printed cost instead of Morph at `announceKicker`; CR 601.2b–c /
601.3 / 702.37a). -/
def validateFrontFaceCast (g : Game) (p : PlayerId) (card : GameObject) (face : CardDef)
    (sneakCost : Option ManaCost := none)
    (origPermOverride : Option PlayPermission := none)
    (excludeIdOverride : Option ObjectId := none) : Except String Unit := do
  let checkId := excludeIdOverride.getD card.id
  -- CR 601.3e / 715.3a: an Adventure is cast with only its alternative (Instant /
  -- Sorcery) characteristics, so a creature-only top-of-library permission (Elven Chorus)
  -- can't cast it.
  if card.zone == .library p && !face.isCreature then
    throw "You may only cast creature spells from the top of your library"
  if g.spellNameForbidden face.name then
    throw s!"Spells named {face.name} can't be cast"
  if face.isLand then
    throw "Lands are played, not cast (CR 305)"
  if !g.graveyardCastThresholdMet p card.id face then
    let n := face.castOnlyIfGraveyardAtLeast.getD 0
    throw s!"{face.name} can be cast only with {n} or more other cards in your graveyard"
  let origPerm := origPermOverride.orElse (fun _ => g.playPermission card)
  if !(g.timingAllowsCast p face (excludeStackId := excludeIdOverride) ||
      origPerm.any (·.ignoreTiming) || sneakCost.isSome) then
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
  if let some err := g.mandatorySacrificeError? p checkId face then
    throw err

/-- Whether `p` may begin to cast `o` as an Adventure (CR 715.3). -/
def canCastAdventure (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  match (g.baseCard o).adventure with
  | none => false
  | some adv =>
    let face := adv.toCardDef
    let fromGraveyard := o.zone == .graveyard o.owner
    let hadFlashbackPerm := fromGraveyard && g.flashbackUntilEot o
    let isFlashbackCast := fromGraveyard && (face.flashback.isSome || hadFlashbackPerm)
    !g.splitSecondOnStack &&
    !g.combatLocksNonManaAbilities &&
    !g.opponentsCantCastOnActiveTurn p &&
    !g.spellNameForbidden face.name &&
    !g.cantCastSpellsThisTurn p &&
    !g.adventureExileForbidsRecast o &&
    -- CR 601.3e / 715.3a: the Adventure's own (Instant / Sorcery) characteristics decide
    -- whether a creature-only library-top permission applies.
    (o.zone != .library p || face.isCreature) &&
    g.mayPlay p o &&
    g.graveyardCastThresholdMet p o.id face &&
    (match g.playPermission o with
     | some perm =>
       (perm.ignoreTiming || g.timingAllowsCast p face) &&
         (!perm.payLifeEqualManaValue || g.canPayLife p face.manaValue)
     | none => g.timingAllowsCast p face) &&
    (g.mandatorySacrificeError? p o.id face).isNone &&
    (!(isFlashbackCast && face.flashbackDiscard) || (g.player p).hand.any (· != o.id)) &&
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

/-- Whether paying this proposed spell or ability may spend Elf-restricted mana
(CR 106.6): Elf spells, and activated abilities of Elf sources. -/
def proposedAllowsElfRestricted (g : Game) (prop : ProposedSpell) : Bool :=
  match prop.kind with
  | .spell =>
    match g.findObject? prop.spellId with
    | some o => g.hasSubtype o .elf
    | none => false
  | .activatedAbility =>
    match prop.sourceId.bind g.findObject? with
    | some src => g.hasSubtype src .elf
    | none => g.hasSubtype prop.original .elf
  | .turnFaceUp => false

/-- Whether paying this proposed spell may spend instant/sorcery-restricted mana. -/
def proposedAllowsInstRestricted (g : Game) (prop : ProposedSpell) : Bool :=
  match prop.kind with
  | .spell =>
    match g.findObject? prop.spellId with
    | some o => g.isInstantOrSorcery o
    | none => false
  | .activatedAbility | .turnFaceUp => false

/-- Object whose types decide Hero / Villain / creature-source restrictions. -/
def proposedRestrictionSource (g : Game) (prop : ProposedSpell) : Option GameObject :=
  match prop.kind with
  | .spell => g.findObject? prop.spellId
  | .activatedAbility =>
    match prop.sourceId.bind g.findObject? with
    | some src => some src
    | none => some prop.original
  | .turnFaceUp => none

/-- Whether paying this proposed spell or ability may spend Hero-restricted
mana (MSH 72): Hero spells, and activated abilities of Hero sources
(including changeling and cards in any zone). -/
def proposedAllowsHeroRestricted (g : Game) (prop : ProposedSpell) : Bool :=
  match g.proposedRestrictionSource prop with
  | some o => g.hasSubtype o .hero
  | none => false

/-- Whether paying this proposed spell or ability may spend Villain-restricted
mana (MSH 73): Villain spells, and activated abilities of Villain sources. -/
def proposedAllowsVillainRestricted (g : Game) (prop : ProposedSpell) : Bool :=
  match g.proposedRestrictionSource prop with
  | some o => g.hasSubtype o .villain
  | none => false

/-- Whether paying this proposed activation may spend creature-restricted mana
(MSH 75). Casting a creature spell does not qualify. -/
def proposedAllowsCreatureRestricted (g : Game) (prop : ProposedSpell) : Bool :=
  match prop.kind with
  | .spell | .turnFaceUp => false
  | .activatedAbility =>
    match g.proposedRestrictionSource prop with
    | some o => g.isCreature o
    | none => false

/-- Whether paying this proposal may spend “can't be spent to cast a
nonartifact spell” mana (MSH 345 / 347): artifact spells, and any
activated ability. -/
def proposedAllowsCantNonartifact (g : Game) (prop : ProposedSpell) : Bool :=
  match prop.kind with
  | .activatedAbility | .turnFaceUp => true
  | .spell =>
    match g.findObject? prop.spellId with
    | some o => g.isArtifact o
    | none => false

/-- What paying `prop` is for, as Reality Fracture mana restrictions see it. -/
def proposedManaSpend (g : Game) (prop : ProposedSpell) : ManaSpend :=
  match prop.kind with
  | .activatedAbility => { equip := prop.activation.any (·.isEquip) }
  | .turnFaceUp => {}
  | .spell =>
    match g.findObject? prop.spellId with
    | some o =>
      { spell := true, fromHand := prop.original.zone == .hand prop.caster
        supertypes := g.supertypes o
        types := g.types o
        subtypes := g.subtypes o }
    | none => {}

/-- Whether mana with restriction `r` may be spent on `prop` (CR 106.6). -/
def restrictionAllowsProposed (g : Game) (r : ManaRestriction) (prop : ProposedSpell) : Bool :=
  match r with
  | .none => true
  | .elf => g.proposedAllowsElfRestricted prop
  | .instantOrSorcery => g.proposedAllowsInstRestricted prop
  | .hero => g.proposedAllowsHeroRestricted prop
  | .villain => g.proposedAllowsVillainRestricted prop
  | .cantNonartifact => g.proposedAllowsCantNonartifact prop
  | .creatureSource => g.proposedAllowsCreatureRestricted prop
  | .fra u => u.allows (g.proposedManaSpend prop)

/-- Mana types `src` can produce that may be spent on `prop` (CR 106.6). -/
def usableManaTypesForProposed (g : Game) (src : GameObject) (types : Array ManaType)
    (prop : ProposedSpell) : Array ManaType :=
  types.filter (fun t => g.restrictionAllowsProposed (g.tapRestrictionOf src t) prop)

/-- Untapped mana sources `p` may activate while paying `prop` (CR 601.2g).
Sources reserved for `{T}`, or whose mana cannot be spent on this spell or
ability, are omitted. -/
def manaSourcesForProposed (g : Game) (p : PlayerId) (prop : ProposedSpell) :
    Array (GameObject × Array ManaType) :=
  (g.manaSources p).filterMap (fun (src, types) =>
    if (prop.tapSource && prop.sourceId == some src.id) || prop.teamworkCreatures.contains src.id then
      none
    else
      let usable := g.usableManaTypesForProposed src types prop
      if usable.isEmpty then none
      else some (src, usable))

/-- Pool after tapping `src` for `t`, including spending restrictions. -/
def poolAfterTap (g : Game) (pool : ManaPool) (src : GameObject) (t : ManaType) :
    ManaPool :=
  addRestrictedMana pool (Array.replicate (g.manaFromTap src t) t) (g.tapRestrictionOf src t)

/-- Restricted mana beyond Elf and instant/sorcery mana that may pay a
cost (CR 106.6). -/
structure ManaAllowances where
  hero : Bool := false
  villain : Bool := false
  cantNonartifact : Bool := false
  creature : Bool := false
  spend : ManaSpend := {}
deriving Inhabited

/-- What restricted mana may pay for `prop`. -/
def proposedAllowances (g : Game) (prop : ProposedSpell) : ManaAllowances :=
  { hero := g.proposedAllowsHeroRestricted prop, villain := g.proposedAllowsVillainRestricted prop
    cantNonartifact := g.proposedAllowsCantNonartifact prop
    creature := g.proposedAllowsCreatureRestricted prop, spend := g.proposedManaSpend prop }

/-- Whether some assignment of types from `sources` pays `cost`. -/
def canPayFromSources (g : Game) (pool : ManaPool) (cost : ManaCost)
    (allowElf allowInst : Bool) (sources : List (GameObject × Array ManaType))
    (a : ManaAllowances := {}) : Bool :=
  match sources with
  | [] => pool.canPay cost allowElf allowInst a.hero a.villain a.cantNonartifact a.creature a.spend
  | (src, types) :: rest =>
    types.any (fun t =>
      g.canPayFromSources (g.poolAfterTap pool src t) cost allowElf allowInst rest a)

/-- Whether tapping `src` for `t` covers more of `cost` than the current pool. -/
def typeHelpsPay (g : Game) (p : PlayerId) (src : GameObject) (t : ManaType)
    (cost : ManaCost) (allowElfRestricted : Bool) (allowInstRestricted : Bool)
    (a : ManaAllowances := {}) : Bool :=
  let amount := g.manaFromTap src t
  if amount == 0 then false
  else
    let pool := (g.player p).manaPool
    let covered (pool : ManaPool) :=
      pool.coveredMana cost allowElfRestricted allowInstRestricted a.hero a.villain
        a.cantNonartifact a.creature a.spend
    covered (g.poolAfterTap pool src t) > covered pool

/-- A mana type among `types` that helps pay remaining symbols of `cost`.
When `src` plus `others` can pay, types that would make the cost unpayable
are omitted so Hidden Lair taps for `{U}` or `{B}` instead of a color another
source already covers. Prefers an unmet colored requirement, then colorless
if it can be spent. -/
def preferredManaType (g : Game) (p : PlayerId) (src : GameObject)
    (types : Array ManaType) (cost : ManaCost) (allowElfRestricted : Bool)
    (allowInstRestricted : Bool := false)
    (others : List (GameObject × Array ManaType) := []) (a : ManaAllowances := {}) :
    Option ManaType :=
  let pool := (g.player p).manaPool
  let helpful := types.filter (fun t =>
    g.typeHelpsPay p src t cost allowElfRestricted allowInstRestricted a)
  let payable :=
    g.canPayFromSources pool cost allowElfRestricted allowInstRestricted
      ((src, types) :: others) a
  let viable :=
    if payable then
      helpful.filter (fun t =>
        g.canPayFromSources (g.poolAfterTap pool src t) cost
          allowElfRestricted allowInstRestricted others a)
    else helpful
  match viable[0]? with
  | none => none
  | some first =>
    match Color.all.find? (fun c =>
      let req := cost.coloredCount c
      let held := pool.usable (.colored c) allowElfRestricted allowInstRestricted a.hero
        a.villain a.cantNonartifact a.creature a.spend
      held < req && viable.contains (.colored c)) with
    | some c => some (.colored c)
    | none =>
      if viable.contains .colorless then some .colorless
      else some first

/-- Whether `(src, t)` is a better next tap than `(bestSrc, bestT)`: avoid
creatures when another source helps, then prefer colorless. Equal ranks keep
the earlier source. -/
def betterManaTap (g : Game) (src : GameObject) (t : ManaType)
    (bestSrc : GameObject) (bestT : ManaType) : Bool :=
  (!g.isCreature src && g.isCreature bestSrc) ||
    (g.isCreature src == g.isCreature bestSrc && t == .colorless && bestT != .colorless)

/-- Next source to tap for `prop`. Noncreatures are chosen before creatures
when both help, and colorless is preferred when that type can be spent.
A flexible source such as Hidden Lair is tapped for `{U}` or `{B}` when
that choice still lets the remaining sources pay. -/
def preferredManaTap (g : Game) (p : PlayerId) (prop : ProposedSpell) :
    Option (GameObject × ManaType) :=
  let allowElf := g.proposedAllowsElfRestricted prop
  let allowInst := g.proposedAllowsInstRestricted prop
  let sources := g.manaSourcesForProposed p prop
  sources.foldl (fun acc (src, types) =>
    let others := sources.filter (fun (o, _) => o.id != src.id) |>.toList
    match g.preferredManaType p src types prop.cost allowElf allowInst others
        (g.proposedAllowances prop) with
    | none => acc
    | some t =>
      match acc with
      | none => some (src, t)
      | some (bestSrc, bestT) =>
        if g.betterManaTap src t bestSrc bestT then some (src, t) else acc) none

def payCost (g : Game) (p : PlayerId) (cost : ManaCost)
    (allowElfRestricted : Bool := false) (allowInstRestricted : Bool := false)
    (allowHeroRestricted : Bool := false) (allowVillainRestricted : Bool := false)
    (allowCantNonartifact : Bool := false)
    (allowCreatureRestricted : Bool := false) (spend : ManaSpend := {})
    (forObject : Option ObjectId := none) :
    Except String Game := do
  let pl := g.player p
  match pl.manaPool.payUnits? cost allowElfRestricted allowInstRestricted
      allowHeroRestricted allowVillainRestricted allowCantNonartifact
      allowCreatureRestricted spend with
  | none => throw s!"{pl.name} cannot pay {cost}"
  | some (_, spentUnits) =>
    return g.record
      (GameEvent.manaSpent g.turnNumber p spentUnits forObject
        (cause := some (.costPayment .mana p forObject)))

/-- Run any deferred mid-resolution post-cast cleanup (`PostCastCleanup`) once
a cast-during-resolution spell finishes casting (`becomeCast`) or reverses
(`reverseProposedSpellCore?`). -/
def runPostCastCleanup (g : Game) : Game :=
  match g.postCastCleanup with
  | none => g
  | some cleanup =>
    let g := g.change (.postCastCleanup none)
    match cleanup with
    | .cascadeBottom caster cardId others =>
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

/-- Core proposal reversal: restores `proposalCheckpoint`, reapplies CR 733.1
irreversible library actions, runs deferred `postCastCleanup`, and reports
whether `Decisions.finishFraChoice` should resume an active continuation
(CR 601.2 / 602.2 / 733.1–733.2). -/
def reverseProposedSpellCore? (g : Game) (resumeContinuation : Bool := false)
    (extraLog : Option String := none) : Except String (Game × Bool) := do
  match g.proposedSpell with
  | none => return (g, false)
  | some prop =>
    let name := (g.player prop.caster).name
    let baseTriggers := (g.proposalCheckpoint.map (·.waitingTriggers.size)).getD 0
    let baseEventSize := (g.proposalCheckpoint.map (·.eventsSize)).getD g.events.size
    let reversed :=
      match prop.kind with
      | .spell => "the casting is reversed (CR 601.2 / 733.1)"
      | .activatedAbility => "the activation is reversed (CR 602.2 / 733.1)"
      | .turnFaceUp => "turning it face up is reversed (CR 116.2b / 702.37e / 733.1)"
    let g ← g.reverseToProposalCheckpoint?
    let hasUnreversedActions := g.events.size > baseEventSize
    let g := g.logMsg s!"{name} cannot pay {prop.cost}; {reversed}"
    let g :=
      match extraLog with
      | some msg => g.logMsg msg
      | none => g
    let g := g.runPostCastCleanup
    let g :=
      if g.pending == .none && g.continuations.isEmpty &&
          g.priority != prop.caster then
        g.change (.priority prop.caster)
      else g
    if resumeContinuation &&
        (!g.continuations.isEmpty || g.pendingReplacement.isSome) then
      return (g, true)
    else if g.pending == .none && g.continuations.isEmpty &&
        (g.waitingTriggers.size > baseTriggers || hasUnreversedActions) then
      return (g.receivePriority prop.caster, false)
    else
      return (g, false)

/-- Clear `.payWard` once a ward cost is paid or declined, draining any active
`pendingReplacement` / `outerPendingReplacements` continuations before finishing
active resolutions, trigger target announcements, or priority (CR 702.21a / 608.2n). -/
def afterWardResolved (g : Game) : Game :=
  let g :=
    match g.pending with
    | .payWard .. => g.change (.pending .none)
    | _ => g
  if (match g.pending with | .chooseReplacement .. => true | _ => false) ||
      g.pendingReplacement.isSome then
    g.chainPendingReplacement .afterWardResolved
  else if let some outer := g.outerPendingReplacements.back? then
    let g := g.changes #[.popOuterPendingReplacement, .pendingReplacement (some outer)]
    g.chainPendingReplacement .afterWardResolved
  else
    let g := g.completeActiveResolutions
    if g.over || g.pending != .none || g.afterRandom != .none then g
    else if g.triggerNeedingTargets.isSome then g.promptTriggerTargetsIfNeeded
    else
      let prio := g.pendingPriority.getD g.activePlayer
      g.receivePriority prio

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
      if g.pending != Pending.none then g
      else
        let alive := ids.filter (fun id =>
          (g.findObject? id).any (fun (o : GameObject) =>
            o.zone == Zone.exile && !g.isLand o))
        let g := g.change (.pendingMayCastFromExile none)
        if q != p || alive.isEmpty || left == 0 then g
        else
          g.beginFraChoice q (.mayCastUpToFromExile alive left)
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
        if castable.isEmpty || castsLeft == 0 then
          let g :=
            if alive.isEmpty then g
            else
              g.withBatch (some (.stateBased .copyOutsideStackOrBf)) fun g =>
                alive.foldl (fun g id =>
                  g.ceaseToExist id (cause := some (.stateBased .copyOutsideStackOrBf))) g
          g.change (.pendingFreeCopies none)
        else
          g.beginFraChoice q (.castCopiesFree alive budget castsLeft)
    | none => g
  if !grantPriority then g
  else if let .chooseReplacement .. := g.pending then
    if g.triggerSequenceRest.isSome || hadOuterReplacement then
      g.chainPendingReplacement .finishFraChoice
    else
      g.chainPendingReplacement (.receivePriority (if hadOpenContinuation then g.activePlayer else p))
  else if g.pending != .none then g
  else if hadOuterReplacement && g.pendingReplacement.isNone then
    g
  else if g.triggerSequenceRest.isSome || g.pendingReplacement.isSome then
    g.chainPendingReplacement .finishFraChoice
  else g.receivePriority (if hadOpenContinuation then g.activePlayer else p)

def becomeCast (g : Game) (p : PlayerId) (spell : GameObject)
    (grantPriority : Bool := true)
    (hadOuterReplacement : Bool := false)
    (hadOpenContinuation : Option Bool := none) : Game :=
  let openCont := g.proposalHadOpenContinuation hadOpenContinuation
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishBecomeCast p spell.id grantPriority hadOuterReplacement openCont)
  else
    let g := if g.proposalCheckpoint.isSome then g.change .clearProposalCheckpoint else g
    let g := g.change (.castingFromTop false)
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
          g.triggerSequenceRest.isSome || g.pendingReplacement.isSome ||
          hadOuterReplacement || !grantPriority ||
          (grantPriority && !openCont && p != g.activePlayer)
      if needsDeferredPostCast then
        let existingOuter? := g.pendingReplacement
        let g := if existingOuter?.isSome then g.change (.pendingReplacement none) else g
        let g := g.chainPendingReplacement
          (.finishPostCast p grantPriority (hadOuterReplacement || existingOuter?.isSome) openCont)
        match existingOuter? with
        | some outer => g.chainPendingReplacement outer.ensureEndsWithFinishFra
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
          let nDamaged :=
            if isSpell && face.costReductionIfTargetDamaged > 0 && o.status.damage > 0 then
              face.costReductionIfTargetDamaged
            else 0
          let nTapped :=
            if isSpell && face.costReductionIfTargetTapped > 0 && o.status.tapped then
              face.costReductionIfTargetTapped
            else 0
          let nAttacking :=
            if !isSpell || !o.status.attacking then 0
            else if face.costReductionIfTargetAttackingNontoken > 0 then
              if o.printed.isToken then 0 else face.costReductionIfTargetAttackingNontoken
            else face.costReductionIfTargetAttacking
          let nCounters :=
            if prop.activation.any (·.costLessPerPlusOneOnTarget) then o.status.plusOnePlusOne
            else 0
          let nPower :=
            match prop.activation.bind (·.costReductionIfTargetPowerAtMost) with
            | some (k, most) => if g.isCreature o && g.power o ≤ most then k else 0
            | none => 0
          let nEquip :=
            if prop.activation.any (·.isEquip) && g.controlledBy o prop.caster then
              (g.staticAbilities o).foldl (fun acc ab =>
                match ab with
                | .equipAbilitiesTargetingThisCostLess k => acc + k
                | _ => acc) 0
            else 0
          let n := nDamaged + nTapped + nAttacking + nCounters + nPower + nEquip
          if n == 0 then g
          else g.changeProposal (.reduceCostBy (ManaCost.ofGeneric n))
        | none => g
      | _ => g

/-- Pay a loyalty cost: put or remove loyalty counters on the source (CR 606.3 / 606.4 / 118.11). -/
def payLoyaltyCost (g : Game) (p : PlayerId) (o : GameObject) (sym : LoyaltySymbol)
    (forObject : Option ObjectId := none) : Game :=
  let k := (sym.counters).getD 0
  let oName := g.name o
  if k > 0 then
    g.withProposalAction .costAction fun g =>
      g.putCountersDeferredLog o.id .loyalty k.natAbs (some p) .countArePutOn
        (cause := some (.costPayment .loyalty p forObject))
  else if k < 0 then
    let g := g.withProposalAction .costAction fun g =>
      g.recordRemoveCounters o.id .loyalty k.natAbs (byPlayer := some p)
        (cause := some (.costPayment .loyalty p forObject))
    g.logMsg s!"{-k} loyalty counter(s) are removed from {oName}"
  else g

/-- Finish the post-loyalty steps (`clearProposalCheckpoint`, `abilityActivated`,
and priority / continuation resumption) of `becomeActivated`. -/
def finishPostLoyaltyActivated (g : Game) (p : PlayerId) (sourceName : String)
    (sourceId : Option ObjectId := none) (activation : Option ActivatedAbility := none)
    (abilityId : Option ObjectId := none)
    (sourceSnap : Option EventObject := none)
    (srcObj? : Option GameObject := none)
    (hadOuterReplacement : Bool := false)
    (openCont : Bool := false) : Game :=
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
  let abilityObjId := abilityId.getD ⟨g.nextObjectId⟩
  let loyaltyDelta : Option Int :=
    match activation.bind (·.cost.loyalty) with
    | some (.plus n) => some (n : Int)
    | some .plusX => some (chosenX : Int)
    | some (.minus n) => some (-(n : Int))
    | some .zero => some 0
    | some .minusX => some (-(chosenX : Int))
    | none => none
  let isPowerUp : Bool :=
    match activation with
    | some ab => ab.powerUp
    | none => srcObj?.any (fun src => (g.baseCard src).activatedAbilities.any (·.powerUp))
  let isBoast := activation == some ActivatedAbility.zemoBoastAbility
  let abilityIdx : Option Nat :=
    match srcObj?, activation with
    | some src, some ab => (g.activatedAbilitiesOf src).findIdx? (· == ab)
    | _, _ => none
  let isExhaust : Bool := activation.any (·.exhaust)
  let g := if g.proposalCheckpoint.isSome then g.change .clearProposalCheckpoint else g
  let g := g.record (GameEvent.abilityActivated g.turnNumber abilityObjId source p
    (.nonMana loyaltyDelta isEquip isPowerUp isBoast abilityIdx isExhaust))
  let g := g.logMsg s!"{(g.player p).name} activates {sourceName}"
  if g.pending != .none then g
  else if hadOuterReplacement && g.pendingReplacement.isNone then
    g
  else if g.triggerSequenceRest.isSome || g.pendingReplacement.isSome then
    g.chainPendingReplacement .finishFraChoice
  else g.receivePriority (if openCont then g.activePlayer else p)

/-- Finish turning a face-down permanent face up once all morph/megamorph/disguise
costs have been paid, deferring `GameEvent.turnedFaceUp`, clearing proposal state,
and granting priority across `Pending.chooseReplacement` (CR 116.2b / 708.8). -/
def completeTurnFaceUp (g : Game) (caster : PlayerId) (spellId : ObjectId)
    (hadOuterReplacement : Bool := false) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishTurnFaceUp caster spellId hadOuterReplacement)
  else
    let clearCkpt : Array EngineChange :=
      if g.proposalCheckpoint.isSome then #[.clearProposalCheckpoint] else #[]
    let g := g.changes (#[.pending .none, .proposedSpell none, .consecutivePasses 0] ++ clearCkpt)
    let g :=
      match g.findObject? spellId with
      | some o =>
        if o.isOnBattlefield && o.status.faceDown then
          let g := g.record
            (GameEvent.turnedFaceUp g.turnNumber (g.snapshot o)
              (cause := .specialAction .turnFaceUp caster))
          g.logMsg s!"{(g.player caster).name} turns {g.name (g.object! spellId)} face up"
        else g
      | none => g
    if g.pending != .none then g
    else if hadOuterReplacement && g.pendingReplacement.isNone then g
    else if g.triggerSequenceRest.isSome || g.pendingReplacement.isSome then
      g.chainPendingReplacement .finishFraChoice
    else
      g.receivePriority caster

def becomeActivated (g : Game) (p : PlayerId) (sourceName : String)
    (sourceId : Option ObjectId := none) (activation : Option ActivatedAbility := none)
    (abilityId : Option ObjectId := none)
    (sourceSnapshot : Option EventObject := none)
    (sourceOriginal : Option GameObject := none)
    (hadOuterReplacement : Bool := false)
    (hadOpenContinuation : Option Bool := none) : Game :=
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
    let localOuter? := g.pendingReplacement
    let hadOuter := hadOuterReplacement || localOuter?.isSome
    let g := if localOuter?.isSome then g.change (.pendingReplacement none) else g
    let g :=
      match activation.bind (·.cost.loyalty) with
      | some sym =>
        let actualSym := if sym == LoyaltySymbol.minusX then LoyaltySymbol.minus chosenX else sym
        match sourceId.bind g.findObject? with
        | some src => g.payLoyaltyCost p src actualSym (forObject := abilityId)
        | none => g
      | none => g
    if let .chooseReplacement .. := g.pending then
      let g := g.chainPendingReplacement (.finishPostLoyaltyActivated p sourceName sourceId
        activation abilityId sourceSnap srcObj? hadOuter openCont)
      match localOuter? with
      | some outer => g.chainPendingReplacement outer.ensureEndsWithFinishFra
      | none => g
    else
      let g :=
        match localOuter? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      g.finishPostLoyaltyActivated p sourceName sourceId activation abilityId sourceSnap
        srcObj? hadOuter openCont

/-- Permanents `p` may sacrifice to pay “sacrifice another creature or artifact”. -/
def sacrificeCreatureOrArtifactChoices (g : Game) (p : PlayerId) (sourceId : ObjectId) :
    Array GameObject :=
  let src := g.findObject? sourceId
  let creatureOrPlaneswalker := src.any (fun s => (g.baseCard s).additionalCostSacrificeCreatureOrPlaneswalker)
  let creatureOnly := src.any (fun s => (g.baseCard s).additionalCostSacrificeCreature)
  g.permanentsOf p |>.filter (fun o =>
    o.id != sourceId &&
      if creatureOrPlaneswalker then g.isCreature o || g.isPlaneswalker o
      else if creatureOnly then g.isCreature o
      else g.isCreature o || g.isArtifact o)

/-- Finish paying the proposed activation once its mana is paid and every
chosen cost is paid: tap, life, and the source's own costs, then put it on
the stack (CR 601.2h–i / 602.2b). -/
def completeActivation (g : Game) (prop : ProposedSpell)
    (hadOuterReplacement : Bool := false)
    (hadOpenContinuation : Option Bool := none) : Except String Game := do
  let openCont := g.proposalHadOpenContinuation hadOpenContinuation
  if let .chooseReplacement .. := g.pending then
    return (g.change (.consecutivePasses 0)).chainPendingReplacement
      (.completeActivation hadOuterReplacement openCont)
  let some sid := prop.sourceId | throw "The ability has no source"
  let x := ((g.findObject? prop.spellId).bind (·.chosenX)).getD 0
  let srcSnap := (g.findObject? sid).map g.snapshot |>.orElse (fun _ => some prop.originalSnapshot)
  let srcName := (g.findObject? sid).map g.name |>.getD (g.name prop.original)
  let localOuter? := g.pendingReplacement
  let hadOuter := hadOuterReplacement || localOuter?.isSome
  let g0 := if localOuter?.isSome then g.change (.pendingReplacement none) else g
  let g ← g0.payActivationExtraCosts prop.caster sid prop.tapSource prop.sacrificeSource
    prop.payLife prop.discardSource prop.activation (if prop.removePlusOneX then x else 0)
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
      | some outer => g.chainPendingReplacement outer
      | none => g
    else g
  let clearPending : Array EngineChange :=
    if paused then #[] else #[.pending .none]
  let g := g.changes (clearPending ++ #[.proposedSpell none, .consecutivePasses 0])
  let g := g.becomeActivated prop.caster srcName prop.sourceId prop.activation
    (abilityId := some prop.spellId)
    (sourceSnapshot := srcSnap)
    (sourceOriginal := some prop.original)
    (hadOuterReplacement := hadOuter)
    (hadOpenContinuation := some openCont)
  let g :=
    if paused then
      match localOuter? with
      | some outer => g.chainPendingReplacement outer.ensureEndsWithFinishFra
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
      let kind := (g.targetingOf spell).kind
      let merged :=
        if newTargets.size == e.targets.size &&
            g.validTargetArrayForEntry e spell kind newTargets (allowUnchangedIllegal := true) then
          newTargets
        else
          Id.run do
            let selfSource := spell.sourceId.orElse (fun _ => if spell.zone == .stack then some spell.id else none)
            let totalSlots := e.targets.size + e.skippedOptionalSlots.size
            let slotIndices : Array Nat :=
              if e.skippedOptionalSlots.isEmpty then (List.range e.targets.size).toArray
              else ((List.range totalSlots).filter (fun s => !e.skippedOptionalSlots.contains s)).toArray
            let mut staged := e.targets
            for j in [0:Nat.min staged.size newTargets.size] do
              let candT := newTargets[j]!
              let actualSlot := slotIndices[j]?.getD j
              if candT == e.targets[j]! ||
                  (g.legalTargetsForAtomicKind e.controller (kind.slotKind actualSlot) selfSource).contains candT then
                staged := staged.set! j candT
            if staged != e.targets &&
                g.validTargetArrayForEntry e spell kind staged (allowUnchangedIllegal := true) then
              return staged
            let mut out := e.targets
            for j in [0:Nat.min out.size newTargets.size] do
              let cand := out.set! j newTargets[j]!
              if g.validTargetArrayForEntry e spell kind cand (allowUnchangedIllegal := true) then
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
  if face.chooseOneOrBoth || isReturnUpToTwoGyModal face then 2
  else
    match face.chooseTwoIfYouControlSubtype with
    | some s => if (g.permanentsOf p).any (fun o => g.hasSubtype o s) then 2 else 1
    | none => 1

/-- Minimum number of modes required for `face` (CR 700.2b): `0` for “choose
up to two”, `1` otherwise. -/
def minModesFor (face : CardDef) : Nat :=
  if isReturnUpToTwoGyModal face then 0 else 1

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
