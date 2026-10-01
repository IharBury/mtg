import Mtg.Engine.Card.Definition.Continuous

/-!
# Action leftovers

Recognizers for one printed action: pumps, draws, counters, mana, enters
replacements, searches, and exile.
-/

namespace Mtg.Engine

namespace CardAction

/-- Untap a creature you control, +P/+T on that target, and maybe attach
if the target is a Dwarf. -/
def leftoverUntapPumpAttach? : CardAction → Option (Int × Int)
  | .sequence [
      .untap ut,
      .continuous effects _,
      .if (.anySubtype _ .dwarf) [.optional (.controller .this) (.attach _eq _to)]
    ] =>
    let youControlCreature :=
      match ut.among? with
      | some who =>
        let s := who.shape
        s.sameController && s.types.eqTypes [.creature]
      | none => false
    if youControlCreature then
      ContinuousEffect.addedPT? effects
    else none
  | _ => none

/-- Untap another target creature you control; if it has the given subtype,
put a +1/+1 counter on it. -/
def leftoverUntapPlusOneIfSubtype? : CardAction → Option String
  | .sequence [
      .untap ut,
      .if (.anySubtype _ st) [.putCounter _ .plusOnePlusOne 1]
    ] =>
    match ut.among? with
    | some who =>
      if who.shape.anotherCreatureYouControl then some st.toString else none
    | none => none
  | _ => none

/-- Draw, then discard a card. -/
def leftoverDrawDiscard? : CardAction → Option Nat
  | .sequence [.draw _who (.nat n), .discard _p 1] => some n
  | _ => none

/-- Put a +1/+1 counter on up to one target creature; a target player gains
that much life. -/
def leftoverPlusOneAndGainLife? : CardAction → Option Nat
  | .sequence [
      .putCounter sel .plusOnePlusOne 1,
      .gainLife who (.nat n)
    ] =>
    let upToOneCreature :=
      match sel with
      | .targets n (.range 0 1) among =>
        among.shape.types.eqTypes [.creature] &&
          match who with
          | .target m .player => n != m
          | _ => true
      | _ => false
    let playerTarget :=
      match who with
      | .target _ .player => true
      | _ => false
    if upToOneCreature && playerTarget then some n else none
  | _ => none

/-- Counter a spell; exile a permanent spell and allow a free cast. -/
def leftoverCounterExile? : CardAction → Bool
  | .sequence [
      .actionId _ (.counter _),
      .continuous (.replace (.putToGraveyard _) _ :: _) _
    ] => true
  | _ => false

/-- Duration “until the end of your next turn” (CR 611.2a). -/
def leftoverUntilEndOfYourNextTurn? : Trigger → Bool
  | .sequence [.turnStart, .endOfPlayerTurn who] =>
    who == .controller .this
  | _ => false

/-- Exile the top card; you may play it until the end of your next turn. -/
def leftoverExileTopPlayUntilEndOfNextTurn? : CardAction → Bool
  | .sequence [
      .actionId id (.exile (.topOfLibrary who 1)),
      .continuous [.canPlay permit (.wasCreatedByAction created)] duration
    ] =>
    id == created &&
      who == .controller .this &&
      permit == .controller .this &&
      leftoverUntilEndOfYourNextTurn? duration
  | _ => false

/-- Attach this Equipment to target creature you control. -/
def leftoverEquipAttach? : CardAction → Bool
  | .attach .this sel =>
    match sel.among? with
    | some among =>
      let s := among.shape
      s.sameController && s.types.eqTypes [.creature]
    | none => false
  | _ => false

/-- Equip `Subtype {cost}` when the attach target names a subtype. -/
def leftoverEquipSubtype? : CardAction → Option String
  | .attach .this sel =>
    if leftoverEquipAttach? (.attach .this sel) then
      match sel.among? with
      | some among => among.includedSubtype?
      | none => none
    else none
  | _ => none

/-- Target creature gets +P/+T; if it would die this turn, exile it instead. -/
def leftoverPumpAndExileIfDies? : CardAction → Option (Int × Int)
  | .continuous effects _ =>
    let pt := ContinuousEffect.foundAddedPT? effects
    let replacesDie :=
      effects.any fun e =>
        match e with
        | .replace (.putToGraveyard _) _ => true
        | _ => false
    if replacesDie then pt else none
  | _ => none

/-- Target creature gets +P/+T and gains lifelink. -/
def leftoverPumpAndLifelink? : CardAction → Option (Int × Int)
  | .continuous effects _ =>
    let pt := ContinuousEffect.foundAddedPT? effects
    let lifelink :=
      effects.any fun e =>
        match e with
        | .gainAbility _ (.keyword .lifelink) => true
        | _ => false
    if lifelink then pt else none
  | _ => none

/-- Creatures target player controls get +P/+T. -/
def leftoverCreaturesTargetPlayerGet? : CardAction → Option (Int × Int)
  | .continuous effects _ =>
    match ContinuousEffect.addedPT? effects, ContinuousEffect.massSelector? effects with
    | some (p, t), some among =>
      match among with
      | .intersection fs =>
        let creature := fs.any fun
          | .cardType .creature => true
          | _ => false
        let targetPlayer := fs.any fun
          | .controlled (.target _ .player) => true
          | _ => false
        if creature && targetPlayer then some (p, t) else none
      | _ => none
    | _, _ => none
  | _ => none

/-- Target player draws cards and loses life. -/
def leftoverTargetPlayerDrawLoseLife? : CardAction → Option (Nat × Nat)
  | .sequence [.draw (.target _ .player) (.nat cards), .loseLife _ (.nat life)] =>
    some (cards, life)
  | _ => none

/-- You draw cards and lose life. -/
def leftoverDrawLoseLifeSelf? : CardAction → Option (Nat × Nat)
  | .sequence [
      .draw (.controller .this) (.nat cards),
      .loseLife (.controller .this) (.nat life)
    ] =>
    some (cards, life)
  | _ => none

/-- Draw a card, lose 1 life, then amass Goblins `n`. -/
def leftoverDrawLoseLifeThenAmass? : CardAction → Option Nat
  | .sequence [
      .draw (.controller .this) 1,
      .loseLife (.controller .this) 1,
      .keyword (.controller .this) (.amass .goblin (.nat n))
    ] => some n
  | _ => none

/-- Return up to one creature card from your graveyard, then amass Goblins `n`. -/
def leftoverReturnCreatureFromGyThenAmass? : CardAction → Option Nat
  | .sequence [.returnToHand sel, .keyword (.controller .this) (.amass .goblin (.nat n))] =>
    match sel with
    | .targets _ (.range 0 1) among | .target _ among =>
      if among.shape.types.eqTypes [.creature] && among.includesInGraveyard then
        some n
      else none
    | _ => none
  | _ => none

/-- Counter the targeted spell, then recruit if its mana value was at most `n`.
The threshold is a constant. The mana value is the greatest mana value of
the target, recorded in a value variable before the spell is countered. -/
def leftoverCounterThenRecruitIfMvAtMost? : CardAction → Option Nat
  | .sequence [
      .defineValueVariable id (.greatestManaValue (.target spellId .spell)),
      .counter (.targetReference spellId'),
      .if (.lessOrEqual (.variable id') threshold)
        [.keyword (.controller .this) .recruit]
    ] =>
    if id == spellId && spellId == spellId' && id == id' then
      valToNat? threshold
    else none
  | _ => none

/-- Target creature gets +P/+T and gains keywords. -/
def leftoverPumpAndGrantKeywords? : CardAction → Option (Int × Int × Keywords)
  | .continuous effects _ =>
    let pt := ContinuousEffect.foundAddedPT? effects
    let kws := grantedKeywords effects
    match pt with
    | some (p, t) =>
      if kws == Keywords.none then none else some (p, t, kws)
    | none => none
  | _ => none

/-- True when a selector names a controller or a target (not “all creatures”). -/
def namesControllerOrTarget : Selector → Bool
  | .controlled _ | .target _ _ | .targets _ _ _ | .targetSet _ _ _ _
  | .targetReference _ | .selected _ _ _ => true
  | .not s => namesControllerOrTarget s
  | .intersection (f :: fs) => namesControllerOrTarget f || namesControllerOrTarget (.intersection fs)
  | .union (f :: fs) => namesControllerOrTarget f || namesControllerOrTarget (.union fs)
  | _ => false

/-- All creatures get +P/+T (not only yours, and not a targeted player's). -/
def leftoverAllCreaturesGet? : CardAction → Option (Int × Int)
  | .continuous effects _ =>
    match ContinuousEffect.addedPT? effects, ContinuousEffect.massSelector? effects with
    | some (p, t), some among =>
      let s := among.shape
      if s.types.eqTypes [.creature] && !s.sameController &&
          !namesControllerOrTarget among then
        some (p, t)
      else none
    | _, _ => none
  | _ => none

/-- Target creature gets +P/+T, then you draw a card. -/
def leftoverPumpThenDraw? : CardAction → Option (Int × Int)
  | .sequence [.continuous effects _, .draw (.controller .this) 1] =>
    match ContinuousEffect.addedPT? effects, ContinuousEffect.targetingSelector? effects with
    | some (p, t), some sel =>
      if sel.toTargetKind == .creature then some (p, t) else none
    | _, _ => none
  | _ => none

/-- Target creature gains vigilance and can't be blocked; draw a card. -/
def leftoverGrantVigilanceUnblockable? : CardAction → Bool
  | .sequence [.continuous effects _, .draw (.controller .this) 1] =>
    let vigil := grantedKeywords effects |>.vigilance
    let unblockable :=
      effects.any fun
        | .forbid (.block .any sel) =>
          match sel with
          | .target _ among => among.shape.types.eqTypes [.creature]
          | .targetReference _ => true
          | _ =>
            match sel.among? with
            | some among => among.shape.types.eqTypes [.creature]
            | none => false
        | _ => false
    vigil && unblockable
  | _ => false

/-- Target creature gets +P/+T, then exile the top card and play it until
the end of your next turn. -/
def leftoverPumpThenExileTopPlay? : CardAction → Option (Int × Int)
  | .sequence [
      .continuous effects _,
      .actionId id (.exile (.topOfLibrary who 1)),
      .continuous [.canPlay permit (.wasCreatedByAction created)] duration
    ] =>
    if leftoverExileTopPlayUntilEndOfNextTurn?
        (.sequence [
          .actionId id (.exile (.topOfLibrary who 1)),
          .continuous [.canPlay permit (.wasCreatedByAction created)] duration
        ]) then
      leftoverTargetPump? effects
    else none
  | _ => none

/-- Target creature can't be blocked this turn. -/
def leftoverTargetCantBeBlocked? : CardAction → Bool
  | .continuous [.forbid (.block .any sel)] _ =>
    match sel with
    | .target _ among => among.shape.types.eqTypes [.creature]
    | _ =>
      match sel.among? with
      | some among => among.shape.types.eqTypes [.creature]
      | none => false
  | _ => false

/-- Tap target creature, then scry and draw. -/
def leftoverTapScryDraw? : CardAction → Option (Nat × Nat)
  | .sequence [.tap sel, .scry _ (.nat scryN), .draw _ (.nat drawN)] =>
    if sel.toTargetKind == .creature then some (scryN, drawN) else none
  | _ => none

/-- Return target spell to its owner's hand, then draw a card. -/
def leftoverReturnSpellDraw? : CardAction → Bool
  | .sequence [.returnToHand sel, .draw _ 1] => sel.toTargetKind == .spell
  | _ => false

/-- Return target spell to its owner's hand. If the gift was promised,
players can't cast spells until end of turn. The promise is an event
since the start of the game (CR 702.174k). -/
def leftoverReturnSpellCantCastIfGift? : CardAction → Bool
  | .sequence [
      .returnToHand (.target _ .spell),
      .if (.happened (.giftPromised .this) .gameStart) [
        .continuous [.forbid (.castSpell .all)] .endOfTurn]
    ] => true
  | _ => false

/-- Destroy target artifact or enchantment; you gain life. -/
def leftoverDestroyArtEnchGainLife? : CardAction → Option Nat
  | .sequence [.destroy sel, .gainLife _ (.nat n)] =>
    if sel.toTargetKind == .artifactOrEnchantment then some n else none
  | _ => none

/-- Destroy target artifact or land; creatures without flying can't block. -/
def leftoverDestroyArtOrLandNonflyers? : CardAction → Bool
  | .sequence [
      .destroy sel,
      .continuous [.forbid (.block (.not (.keyword .flying)) _)] _
    ] =>
    sel.toTargetKind == .artifactOrLand
  | _ => false

/-- Target creature becomes an artifact and gains indestructible. -/
def leftoverBecomeArtifactIndestructible? : CardAction → Bool
  | .continuous effects _ =>
    let becomesArtifact :=
      effects.any fun
        | .gainType sel .artifact => sel.toTargetKind == .creature
        | _ => false
    becomesArtifact && (grantedKeywords effects).indestructible
  | _ => false

/-- Put a +1/+1 counter on target creature; it gains lifelink and
indestructible. -/
def leftoverPlusOneLifelinkIndestructible? : CardAction → Bool
  | .sequence [.putCounter sel .plusOnePlusOne 1, .continuous effects _] =>
    let kws := grantedKeywords effects
    sel.toTargetKind == .creature && kws.lifelink && kws.indestructible
  | _ => false

/-- A creature you control deals damage equal to its power to an opponent's
creature. -/
def leftoverCreatureYouControlDealsPowerToOppCreature? : CardAction → Bool
  | .dealDamage src dest amount =>
    amount == .greatestPower src &&
      src.toTargetKind == .creatureYouControl && dest.toTargetKind == .oppCreature
  | _ => false

/-- Put a +1/+1 counter on a creature you control; it gains trample and
hexproof. -/
def leftoverPlusOnePlusOneTrampleHexproof? : CardAction → Bool
  | .sequence [
      .putCounter sel .plusOnePlusOne 1,
      .continuous effects _
    ] =>
    let youControlCreature :=
      match sel.among? with
      | some who =>
        let s := who.shape
        s.sameController && s.types.eqTypes [.creature]
      | none => false
    let kws := grantedKeywords effects
    youControlCreature && kws.trample && kws.hexproof
  | _ => false

/-- Put +1/+1 counters on a creature you control; it gains vigilance. -/
def leftoverPlusOneVigilance? : CardAction → Option Nat
  | .sequence [
      .putCounter sel .plusOnePlusOne (.nat n),
      .continuous effects _
    ] =>
    let youControlCreature :=
      match sel.among? with
      | some who =>
        let s := who.shape
        s.sameController && s.types.eqTypes [.creature]
      | none => false
    let kws := grantedKeywords effects
    if youControlCreature && kws.vigilance then some n else none
  | _ => none

/-- Become a creature of the given subtype and gain static abilities whose
power and toughness are each equal to the number of lands you control. -/
def leftoverBecomeSubtypeWithLandsPT? : CardAction → Option String
  | .continuous effects _ =>
    let subtype :=
      effects.findSome? fun
        | .gainSubtype _ st => some st.toString
        | _ => none
    let becomesCreature :=
      effects.any fun
        | .gainType _ .creature => true
        | _ => false
    let grantsLandsPT :=
      effects.any (grantsLandsCharacteristic true) &&
        effects.any (grantsLandsCharacteristic false)
    if becomesCreature && grantsLandsPT then subtype else none
  | _ => none

/-- Spend this mana only on Elf spells and activated abilities of Elf
sources. -/
def leftoverElfRestrictedSpend? : Trigger → Bool
  | .not
      (.or
        (.castSpell (.subtype .elf))
        (.activateAbility (.subtype .elf))) => true
  | _ => false

/-- Spend this mana only to cast an instant or sorcery spell. -/
def leftoverInstantOrSorcerySpend? : Trigger → Bool
  | .not (.castSpell among) =>
    among.shape.types.eqTypes [.instant, .sorcery]
  | .not (.or (.castSpell a) (.castSpell b)) =>
    (a == .cardType .instant && b == .cardType .sorcery) ||
      (a == .cardType .sorcery && b == .cardType .instant)
  | _ => false

/-- Tap and add mana of any color equal to this object's power, spendable
only on Elf spells and Elf sources. -/
def leftoverTapAddAnyColorEqualToPower? (costs : List Cost) : CardAction → Bool
  | .sequence [
      .actionId id (.addManaOfOneColor who syms amount),
      .continuous [.forbid (.spendManaCreatedByAction spendId restriction)] _
    ] =>
    id == spendId &&
      leftoverElfRestrictedSpend? restriction &&
      Cost.hasTapSymbol costs &&
      who == .controller .this &&
      syms == ManaSymbol.anyColor &&
      (amount == .greatestPower .this || amount == .greatestPower (.source .this))
  | _ => false

/-- `{T}: Add` one mana of any color, spendable only on instant and
sorcery spells. -/
def leftoverTapAddAnyColorForInstantOrSorcery? (costs : List Cost) : CardAction → Bool
  | .sequence [
      .actionId id (.addManaOfOneColor who syms 1),
      .continuous [.forbid (.spendManaCreatedByAction spendId restriction)] _
    ] =>
    id == spendId &&
      leftoverInstantOrSorcerySpend? restriction &&
      costs == [.tapSymbol] &&
      who == .controller .this &&
      syms == ManaSymbol.anyColor
  | _ => false

/-- Mana produced when this symbol is added to a pool (CR 106.4). -/
def addedManaType? : ManaSymbol → Option ManaType
  | .colored c => some (.colored c)
  | .colorless => some .colorless
  | .generic _ | .hybrid _ _ | .monoOrDouble _ | .monoOrColorless _
  | .phyrexianMono _ | .phyrexianGeneric | .phyrexianHybrid _ _ | .x | .snow =>
    none

/-- Types added by a list of symbols, or `none` if any symbol is not
addable mana. -/
def addedManaTypes? (syms : List ManaSymbol) : Option (Array ManaType) :=
  let ts := syms.filterMap addedManaType?
  if ts.length == syms.length then some ts.toArray else none

/-- One `addMana` option: `who` adds a single listed type. -/
def leftoverAddManaOne? (who : Selector) : CardAction → Option ManaType
  | .addMana gainer [sym] =>
    if gainer == who then addedManaType? sym else none
  | _ => none

/-- `{T}: Add` the listed types, all at once (Llanowar Elves). -/
def leftoverTapAddMana? (costs : List Cost) (action : CardAction) :
    Option (Array ManaType) :=
  match action with
  | .addMana who syms =>
    if costs == [.tapSymbol] && who == .controller .this then
      addedManaTypes? syms
    else none
  | _ => none

/-- `{T}: Add {A} or {B}` as a tap-only mana ability. Each listed action
must be `addMana` of one symbol; the player chooses one. -/
def leftoverTapAddOneOf? (costs : List Cost) : CardAction → Option (Array ManaType)
  | .playerSelectAction who (.range 1 1) actions =>
    if costs == [.tapSymbol] && who == .controller .this && actions.length >= 2 then
      let ts := actions.filterMap (leftoverAddManaOne? who)
      if ts.length == actions.length then some ts.toArray else none
    else none
  | _ => none

/-- `{T}: Add {C} for each Food you control.` -/
def leftoverTapAddManaForEach? (costs : List Cost) : CardAction → Option TapAddForEach
  | .forEachVariable _ (.intersection [.zone .battlefield, .subtype st, .controlled (.controller .this)])
      [.addMana who [sym]] =>
    if costs == [.tapSymbol] && who == .controller .this then
      (addedManaType? sym).map fun m => { mana := m, subtype := st.toString }
    else none
  | _ => none

/-- `{T}: Add two mana in any combination of {U}, {B}, and/or {R}.` -/
def leftoverTapAddTwoAmong? (costs : List Cost) : CardAction → Option (Array ManaType)
  | .addManaInAnyCombination who syms (.nat 2) =>
    if costs == [.tapSymbol] && who == .controller .this && syms.length >= 2 then
      (syms.mapM addedManaType?).map List.toArray
    else none
  | _ => none

/-- `{T}, Pay 1 life: Add {B} or {R}.` -/
def leftoverTapPayLifeAddOneOf? (costs : List Cost) (action : CardAction) :
    Option (Nat × Array ManaType) :=
  match costs with
  | [.tapSymbol, .life k] =>
    if k == 0 then none else (leftoverTapAddOneOf? [.tapSymbol] action).map (k, ·)
  | _ => none

/-- This land entered this turn or you control a basic land. -/
def leftoverEnteredThisTurnOrBasic? : Condition → Bool
  | .not (.and (.not (.happened (.enter (.source .this)) .turnStart))
      (.not (.any (.intersection [.zone .battlefield, .cardType .land, .supertype .basic, you])))) =>
    you == .controlled (.controller .this)
  | _ => false

/-- `A, B, and C`: an English list with a serial comma. -/
def englishAndList : List String → String
  | [] => ""
  | [a] => a
  | [a, b] => s!"{a} and {b}"
  | xs => ", ".intercalate xs.dropLast ++ ", and " ++ xs.getLast!

/-- `{T}: Add {R}{R}. Spend this mana only to cast Dwarf, Equipment, and Saga
spells.` The mana and the printed spell restriction. -/
def leftoverTapAddRestricted? (costs : List Cost) : CardAction → Option (Array ManaType × String)
  | .sequence [
      .actionId id (.addMana who syms),
      .continuous
        [.forbid (.spendManaCreatedByAction id'
          (.not (.castSpell (.intersection [.spell, .union kinds]))))]
        .endOfTurn] =>
    let subtypes := kinds.filterMap fun
      | .subtype st => some st.toString
      | _ => none
    if costs == [.tapSymbol] && who == .controller .this && id == id' &&
        !syms.isEmpty && subtypes.length == kinds.length then
      (syms.mapM addedManaType?).map fun ms =>
        (ms.toArray, englishAndList subtypes ++ " spells")
    else none
  | _ => none

/-- Add one mana of any color. -/
def leftoverAddAnyColor? : CardAction → Bool
  | .addManaOfOneColor _ syms 1 => syms == ManaSymbol.anyColor
  | _ => false

/-- Replacement “this enters tapped”. -/
def leftoverEntersTapped? : List CardAction → Bool
  | [.putOntoBattlefieldInState obj [.tapped]] =>
    obj == .this || obj == .source .this
  | _ => false

/-- Replacement “as this enters, choose a creature type”: this object's
controller makes the numbered choice, then it enters (CR 614.12). -/
def leftoverChooseCreatureTypeAsEnters? : List CardAction → Bool
  | [.actionId _ (.chooseCreatureType who), .keepReplacedAction] =>
    who == .controller .this
  | _ => false

/-- Replacement “this enters with X +1/+1 counters”. -/
def leftoverEntersWithXPlusOne? : List CardAction → Bool
  | [.putCounter who .plusOnePlusOne .x, .keepReplacedAction] =>
    who == .this || who == .source .this
  | _ => false

/-- Replacement “this enters with a hope counter for each creature you control”. -/
def leftoverEntersWithHopePerCreature? : List CardAction → Bool
  | [.putCounter who (.hope) (.count among), .keepReplacedAction] =>
    (who == .this || who == .source .this) &&
      among == .intersection [
        .zone .battlefield, .cardType .creature, .controlled (.controller .this)]
  | _ => false

/-- The Ruinous Wrecking Crew's four “choose up to X” modes, in printed order. -/
def wreckingCrewModes? : List CardAction → Bool
  | [
      .sequence [
        .discard (.controller .this) (.nat 1),
        .draw (.controller .this) (.nat 1)],
      .loseLife (.target _ (.opponent (.controller .this))) (.nat 2),
      .destroy (.target _ (.intersection [.zone .battlefield, .token])),
      .forEachVariable id .player
        [.sacrifice (.selected (.variable id') (.range 1 1) among)]
    ] =>
    id == id' &&
      among == .intersection [
        .zone .battlefield, .cardType .creature, .controlled (.variable id)]
  | _ => false

/-- Heal all marked damage on this, then perform the replaced action. -/
def leftoverHealThenKeepReplaced? : List CardAction → Bool
  | [.healAllDamage who, .keepReplacedAction] =>
    who == .this || who == .source .this
  | _ => false

/-- Put +1/+1 counters on a targeted creature you control, optionally of
listed subtypes. -/
def leftoverPlusOneOnTarget? : CardAction → Option Effect
  | .putCounter sel .plusOnePlusOne (.nat n) =>
    match sel.among? with
    | some among =>
      if among.shape.sameController && among.shape.types.eqTypes [.creature] then
        some (Effect.plusOneOnTarget n among.includedSubtypes.toArray)
      else none
    | none => none
  | _ => none

/-- Set this source's base power and toughness to printed integers. -/
def leftoverSourceSetBasePT? : List ContinuousEffect → Option (Int × Int)
  | [.setBasePower who p, .setBaseToughness who' t] =>
    if (who == .source .this || who == .this) && who' == who then
      match valToInt? p, valToInt? t with
      | some p, some t => some (p, t)
      | _, _ => none
    else none
  | _ => none

/-- Set another creature you control's base power and toughness to the
greatest power and toughness of this source. Target `n` is declared once. -/
def leftoverSetOtherBasePT? : List ContinuousEffect → Bool
  | [.setBasePower who (Value.greatestPower (.source .this)),
     .setBaseToughness who' (Value.greatestToughness (.source .this))] =>
    match who with
    | .targets n (.range 0 1) among =>
      who' == .targetReference n && among.shape.anotherCreatureYouControl
    | _ => false
  | _ => false

/-- Nested search actions: put a basic land onto the battlefield tapped,
or reveal a found card and put it into hand. -/
def leftoverSearchActions? : List CardAction → Option Effect
  | [.putOntoBattlefieldInState sel [.tapped]] =>
    match sel.selectedAmong? with
    | some among =>
      if among.basicLandInLibrary then some Effect.searchBasicLandTapped else none
    | none => none
  | [.defineSelectorVariable id sel, .reveal (.variable id'), .returnToHand (.variable id'')] =>
    if id == id' && id == id'' then
      match sel.selectedAmong? with
      | some among =>
        if among.basicLandInLibrary then some Effect.searchBasicLandToHand
        else if among.legendaryCreatureInLibrary then
          some Effect.searchLegendaryCreatureToHand
        else
          match among.includedSubtype? with
          | some t =>
            if among.includesInLibrary then some (Effect.searchLandTypeToHand t) else none
          | none => none
      | none => none
    else none
  | [
      .defineSelectorVariable id sel,
      .reveal (.variable id'),
      .putOntoBattlefieldInState
        (.selected _ (.range 1 1) (.variable id'')) [.tapped],
      .returnToHand (.variable id''')
    ] =>
    if id == id' && id == id'' && id == id''' then
      match sel.selectedAmong? with
      | some among =>
        if among.basicLandInLibrary then some Effect.searchTwoBasicsSplit else none
      | none => none
    else none
  | _ => none

/-- Search a library, act on the found cards, then shuffle. -/
def leftoverSearchLibraryThenShuffle? : CardAction → Option Effect
  | .searchLibraryThenShuffle _ actions => leftoverSearchActions? actions
  | _ => none

/-- Each player sacrifices a creature they choose. -/
def leftoverEachPlayerSacrificesCreature? : CardAction → Bool
  | .forEachVariable n among [
      .sacrifice
        (.selected chooser (.range 1 1) sacAmong)
    ] =>
    among == .player &&
      chooser == .variable n &&
      sacAmong.shape.types.eqTypes [.creature]
  | _ => false

/-- Each opponent loses N life and you gain N life. -/
def leftoverEachOpponentLoseLifeYouGain? : CardAction → Option Nat
  | .sequence [.loseLife dest (.nat n), .gainLife who (.nat m)] =>
    if who == .controller .this && n == m then
      match dest with
      | .opponent (.controller .this) => some n
      | _ => none
    else none
  | _ => none

/-- Owner puts the targeted opponent creature into their library second
from the top or on the bottom, then up to one target creature you control
connives. -/
def leftoverOwnerPutsLibraryThenConnive? : CardAction → Bool
  | .sequence [
      .playerSelectAction chooser (.range 1 1)
        [.putIntoLibraryFromTop t1 2, .putOnBottomOfLibrary t2],
      .keyword who (.connive (.nat 1))
    ] =>
    match t1 with
    | .target n among =>
      t2 == .targetReference n &&
        among.toTargetKind == .oppCreature &&
        chooser == .owner (.targetReference n) &&
        match who with
        | .targets _ (.range 0 1) dest =>
          dest.shape.sameController && dest.shape.types.eqTypes [.creature]
        | _ => false
    | _ => false
  | _ => false

/-- Put +1/+1 counters on each other permanent you control of a subtype. -/
def leftoverPlusOneOnEachOtherSubtype? : CardAction → Option Effect
  | .putCounter sel .plusOnePlusOne (.nat n) =>
    if sel.among?.isNone then
      match sel.shape.anotherSubtypeYouControl with
      | some st => some (Effect.plusOneOnEachOtherSubtype st n)
      | none => none
    else none
  | _ => none

/-- Sacrifice one matching permanent the player chooses, not every match. -/
def leftoverSacrificeOneArtifact? : Selector → Bool
  | .selected _ (.range 1 1) among => among.shape.types.eqTypes [.artifact]
  | _ => false

/-- You may sacrifice an artifact or discard a card. If you do, draw. -/
def leftoverMaySacArtifactOrDiscardDraw? : CardAction → Option Nat
  | .sequence [
      .optional (.controller .this)
        (.actionId id
          (.playerSelectAction _ (.range 1 1) [
            .sacrifice sac,
            .discard _ 1])),
      .if (.happened (.actionWithId id') _) [.draw _ (.nat n)]
    ] =>
    if id == id' && leftoverSacrificeOneArtifact? sac then some n else none
  | _ => none

/-- Draw three cards, then discard two unless you discard an artifact. -/
def leftoverDrawThreeDiscardUnlessArtifact? : CardAction → Option Bool
  | .sequence [
      .draw _ 3,
      .preventable who [.discard art] (.discard _ 2)
    ] =>
    if who == .controller .this && art.shape.types.eqTypes [.artifact] then
      some true
    else none
  | _ => none

/-- Choose up to two: return an artifact, creature, enchantment, or land
card from your graveyard to your hand. -/
def leftoverReturnUpToTwoGyModal? : CardAction → Option Bool
  | .playerSelectAction _ (.range 0 2) modes =>
    let gyReturns :=
      modes.all fun
        | .returnToHand sel => Selector.includesInGraveyard sel
        | _ => false
    if modes.length == 4 && gyReturns then some true else none
  | _ => none

/-- Target player gains life, searches a basic land onto the battlefield
tapped, and you put a +1/+1 counter on up to one creature. -/
def leftoverGainLifeSearchBasicPlusOne? : CardAction → Option Nat
  | .sequence [
      .gainLife who (.nat n),
      .searchLibraryThenShuffle _ actions,
      .putCounter sel .plusOnePlusOne 1
    ] =>
    let playerNum : Option Nat :=
      match who with
      | .target n .player => some n
      | _ => none
    let player := playerNum.isSome || who == .player
    let searchOk := leftoverSearchActions? actions == some Effect.searchBasicLandTapped
    let creatureNum : Option Nat :=
      match sel with
      | .targets n (.range 0 1) among =>
        if among.shape.types.eqTypes [.creature] then some n else none
      | .target n among =>
        if among.shape.types.eqTypes [.creature] then some n else none
      | _ => none
    let numsOk :=
      match playerNum, creatureNum with
      | some p, some c => p != c
      | _, _ => creatureNum.isSome
    if player && searchOk && numsOk then some n else none
  | _ => none

/-- Source gets +P/+0 and creatures you control gain trample. -/
def leftoverSourceGetsAndTeamTrample? (effects : List ContinuousEffect) : Option Int :=
  let sourceEffects :=
    effects.filter fun e =>
      match e with
      | .addPower (.source .this) _ | .addToughness (.source .this) _ => true
      | _ => false
  let pt :=
    match ContinuousEffect.foundAddedPT? sourceEffects with
    | some (p, 0) => some p
    | _ => none
  let trample :=
    effects.any fun
      | .gainAbility among (.keyword .trample) =>
        among.shape.sameController && among.shape.types.eqTypes [.creature]
      | _ => false
  if trample then pt else none

/-- Put a +1/+1 counter on target creature; it gains lifelink. -/
def leftoverPlusOneAndLifelinkTarget? : CardAction → Bool
  | .sequence [.putCounter sel .plusOnePlusOne 1, .continuous effects _] =>
    let kws := grantedKeywords effects
    sel.toTargetKind == .creature && kws.lifelink && !kws.indestructible
  | _ => false

/-- Choose tap or untap target nonland permanent. -/
def leftoverTapOrUntapNonland? : List CardAction → Bool
  | [.tap s1, .untap s2] | [.untap s1, .tap s2] =>
    s1.toTargetKind == .nonland && s2.toTargetKind == .nonland
  | _ => false

/-- Choose tap target opponent creature or untap target creature you
control. -/
def leftoverTapOppOrUntapYours? : List CardAction → Bool
  | [.tap s1, .untap s2] =>
    s1.toTargetKind == .oppCreature && s2.toTargetKind == .creatureYouControl
  | [.untap s1, .tap s2] =>
    s1.toTargetKind == .creatureYouControl && s2.toTargetKind == .oppCreature
  | _ => false

/-- Choose: +1/+1 on up to two creatures, or return an artifact or
enchantment card from your graveyard. -/
def leftoverPlusOnesOrReturnArtEnch? : List CardAction → Bool
  | [a, b] =>
    let plusOnes (x : CardAction) : Option Nat :=
      match x with
      | .putCounter (.targets n (.range 0 2) among) .plusOnePlusOne 1 =>
        if among.shape.types.eqTypes [.creature] then some n else none
      | _ => none
    let ret (x : CardAction) : Option Nat :=
      match x with
      | .returnToHand (.target n among) =>
        if Selector.includesInGraveyard among &&
            (among.toTargetKind == .artifactOrEnchantment ||
              among.toTargetKind == .permanent) then
          some n
        else none
      | _ => none
    match plusOnes a, ret b with
    | some n, some m => n != m
    | _, _ =>
      match plusOnes b, ret a with
      | some n, some m => n != m
      | _, _ => false
  | _ => false

/-- Attach target Equipment you control to up to one target creature you
control. -/
def leftoverAttachTargetEquipment? : CardAction → Bool
  | .attach eq cre =>
    let destOk (dest : Selector) : Bool :=
      dest.shape.sameController && dest.shape.types.eqTypes [.creature]
    match eq.among?, cre with
    | some among, .targets _ (.range 0 1) dest =>
      Selector.leftoverDistinctTargetNumbers eq cre &&
        among.shape.sameController &&
        among.includedSubtype? == some "Equipment" &&
        destOk dest
    | some among, .target _ dest =>
      Selector.leftoverDistinctTargetNumbers eq cre &&
        among.shape.sameController &&
        among.includedSubtype? == some "Equipment" &&
        destOk dest
    | _, _ => false
  | _ => false

/-- Battlefield states that are exactly tapped (CR 110.5). -/
def leftoverTappedOnly : List CardState → Bool
  | [.tapped] => true
  | _ => false

/-- Battlefield states that are tapped and attacking (order-independent). -/
def leftoverTappedAndAttacking : List CardState → Bool
  | [.tapped, .attacking] => true
  | [.attacking, .tapped] => true
  | _ => false

/-- True when the condition is that this object's host is legendary. -/
def leftoverHostIsLegendary : Condition → Bool
  | .any (.intersection fs) =>
    fs.contains (.hostOf .this) && fs.contains (.supertype .legendary)
  | _ => false

/-- Battlefield states that are exactly tapped under the selected object's
owner's control (order-independent). -/
def leftoverTappedUnderOwner (obj : Selector) : List CardState → Bool
  | [.tapped, .controlled who] => who == .owner obj
  | [.controlled who, .tapped] => who == .owner obj
  | _ => false

/-- Exile then return the same objects tapped under their owner's control. -/
def leftoverExileThenReturnTapped? : CardAction → Option Selector
  | .sequence [
      .actionId id (.exile sel),
      .putOntoBattlefieldInState (.wasCreatedByAction id') states
    ] =>
    if id == id' && leftoverTappedUnderOwner (.wasCreatedByAction id') states then
      some sel
    else none
  | _ => none

/-- Two target creatures and/or lands this object's controller controls. -/
def leftoverTwoCreaturesOrLandsYouControl? : Selector → Bool
  | .targets _ (.range (.nat 2) (.nat 2)) among =>
    let s := among.shape
    s.mustBePermanent && s.sameController &&
      s.types.eqTypes [.creature, .land] &&
      !s.other && s.subtype.isNone && !s.token && !s.nontoken &&
      !s.opponentControls && !s.flying && !s.tapped &&
      s.powerAtLeast.isNone && s.powerAtMost.isNone
  | _ => false

/-- Exile two creatures and/or lands you control, then return them under
their owner's control. -/
def leftoverExileThenReturnYouControl? : CardAction → Bool
  | .sequence [
      .actionId id (.exile sel),
      .putOntoBattlefieldInState (.wasCreatedByAction id')
        [.controlled who]
    ] =>
    id == id' && who == .owner (.wasCreatedByAction id) &&
      leftoverTwoCreaturesOrLandsYouControl? sel
  | _ => false

/-- Find, reveal, and hold out a basic land while searching so shuffle
does not mix it back in. -/
def leftoverSearchBasicHoldOut? : List CardAction → Option Nat
  | [.defineSelectorVariable id sel, .reveal (.variable id'), .holdOutInLibrary (.variable id'')] =>
    if id == id' && id == id'' then
      match sel.selectedAmong? with
      | some among => if among.basicLandInLibrary then some id else none
      | none => none
    else none
  | _ => none

/-- Search a basic land, hold it out, shuffle, then put that card on top. -/
def leftoverSearchBasicOnTop? : CardAction → Bool
  | .sequence [
      .searchLibraryThenShuffle _ actions,
      .putOnTopOfLibrary (.variable id)
    ] => leftoverSearchBasicHoldOut? actions == some id
  | _ => false

/-- Keyword actions that compile to a named `Effect`. -/
def leftoverKeywordAction? : Keyword → Option Effect
  | .recruit => some Effect.recruit
  | .amass .goblin (.nat n) => some (Effect.amassGoblins n)
  | .amass .orc (.nat n) => some (Effect.ofTrigger (.amassOrcs n))
  | .connive (.nat 1) => some Effect.connive
  | .harness => some Effect.harnessInfinityStone
  | _ => none

/-- Exile up to one other nonland permanent you control, then return that
card under its owner's control. The ∞ ability of The Mind Stone. -/
def leftoverHarnessFlicker? : CardAction → Bool
  | .sequence [
      .actionId id (.exile sel),
      .putOntoBattlefieldInState (.wasCreatedByAction id')
        [.controlled who]
    ] =>
    id == id' && who == .owner (.wasCreatedByAction id) &&
      match sel with
      | .targets _ (.range (.nat 0) (.nat 1)) among =>
        let s := among.shape
        s.other && s.nonland && s.sameController && s.mustBePermanent &&
          s.types == .any && !s.token && !s.nontoken && s.subtype.isNone &&
          !s.opponentControls && !s.tapped && !s.flying && !s.attacking
      | _ => false
  | _ => false

end CardAction

end Mtg.Engine
