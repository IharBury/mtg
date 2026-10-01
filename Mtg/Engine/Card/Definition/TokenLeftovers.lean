import Mtg.Engine.Card.Definition.ActionLeftovers

/-!
# Token and enters leftovers

`TokenParts` recovers a `TokenKind` from printed token characteristics.
The recognizers after it cover token creation, enters-the-battlefield
actions, and mill-then-put.
-/

namespace Mtg.Engine

namespace CardAction

/-- Flattened token characteristics used to recover a `TokenKind`. -/
structure TokenParts where
  name : String := ""
  types : List CardType := []
  subtypes : List String := []
  colors : ColorSet := {}
  power : Option Nat := none
  toughness : Option Nat := none
  keywords : Keywords := Keywords.none
deriving Repr, Inhabited, BEq

def collectTokenParts (parts : List CardPart) : TokenParts :=
  parts.foldl
    (fun acc p =>
      match p with
      | .name n => { acc with name := n }
      | .type t => { acc with types := acc.types ++ [t] }
      | .subtype s => { acc with subtypes := acc.subtypes ++ [s.toString] }
      | .colorIndicator cs =>
        { acc with colors := cs.foldl ColorSet.insert acc.colors }
      | .power n => { acc with power := some n }
      | .toughness n => { acc with toughness := some n }
      | .ability (.keyword k) =>
        { acc with keywords := acc.keywords.merge k.toKeywords }
      | _ => acc)
    {}

/-- True when the collected color indicator is exactly that color. -/
def leftoverIsColor (p : TokenParts) (c : Color) : Bool :=
  p.colors == ColorSet.singleton c

/-- The selected player is this object's controller (“you create”). -/
def leftoverYou : Selector → Bool
  | .controller .this => true
  | _ => false

/-- Search a basic land onto the battlefield tapped. You may behold a subtype.
If you do, untap that land (CR 701.4 / 701.4b). The selector variable is
the library card. The land on the battlefield is `affectedByAction` of the
numbered `putOntoBattlefieldInState`. The behold is the other numbered
action. -/
def leftoverSearchBasicBeholdUntap? : CardAction → Option String
  | .sequence [
      .searchLibraryThenShuffle who [
        .defineSelectorVariable id
          (.selected chooser (.range 1 1) among),
        .actionId putId
          (.putOntoBattlefieldInState (.variable id') [.tapped])],
      .optional who'
        (.actionId beholdId (.keyword actor (.behold st))),
      .if (.happened (.actionWithId beholdId') .gameStart)
        [.untap (.affectedByAction putId')]
    ] =>
    if leftoverYou who && leftoverYou chooser && leftoverYou who' &&
        leftoverYou actor && id == id' && putId == putId' &&
        beholdId == beholdId' && putId != beholdId &&
        among.basicLandInLibrary then
      some st.toString
    else none
  | _ => none

/-- Destroy target creature, then surveil 1. -/
def leftoverDestroyCreatureSurveil? : CardAction → Bool
  | .sequence [.destroy sel, .surveil who 1] =>
    sel.toTargetKind == .creature && leftoverYou who
  | _ => false

/-- Printed Redwing token: legendary 1/1 blue Bird Scout with flying and
“Whenever Redwing attacks, surveil 1.” -/
def leftoverRedwingToken? (parts : List CardPart) : Bool :=
  let p := collectTokenParts parts
  let legendary :=
    parts.any fun
      | .supertype .legendary => true
      | _ => false
  let attackSurveil :=
    parts.any fun
      | .ability (.triggered (.attack .this .all) (.surveil who 1)) =>
        leftoverYou who
      | _ => false
  p.name == "Redwing" && legendary && p.types.contains .creature &&
    p.subtypes.contains "Bird" && p.subtypes.contains "Scout" &&
    leftoverIsColor p .blue && p.power == some 1 && p.toughness == some 1 &&
    p.keywords.flying && attackSurveil

/-- This object or its source, for spell-shaped keyword compile. -/
def leftoverThis : Selector → Bool
  | .this | .source .this => true
  | _ => false

/-- The source of this ability on the stack (CR 113.7), not the ability itself. -/
def leftoverSourceThis : Selector → Bool
  | .source .this => true
  | _ => false

/-- Opponents of this object's controller. -/
def leftoverOpponents : Selector → Bool
  | .opponent who => leftoverYou who
  | _ => false

/-- A numbered target that is a creature you control. -/
def leftoverCreatureYouControlTarget? : Selector → Bool
  | .target _ among =>
    among.shape.sameController && among.shape.types.eqTypes [.creature]
  | _ => false

/-- The host of Equipment you control (an equipped creature you control). -/
def leftoverEquippedCreatureYouControl : Selector → Bool
  | .hostOf among =>
    among.shape.sameController && among.includedSubtype? == some "Equipment"
  | _ => false

/-- Match printed token characteristics to a modeled `TokenKind`. -/
def leftoverTokenKind? (parts : List CardPart) : Option TokenKind :=
  let p := collectTokenParts parts
  let has (st : String) : Bool := p.subtypes.contains st
  if has "Treasure" then some .treasure
  else if has "Food" then some .food
  else if has "Clue" then some .clue
  else if p.name == "Vibranium" then some .vibranium
  else if p.types.contains .creature then
    match p.power, p.toughness with
    | some 2, some 2 =>
      if has "Dwarf" && leftoverIsColor p .red then some .dwarf
      else if has "Wolf" then some .wolf
      else if has "Bear" then some .bear
      else if has "Robot" && has "Villain" then some .robotVillain22
      else none
    | some 1, some 1 =>
      if has "Spirit" && p.keywords.flying && leftoverIsColor p .white then
        some .spirit
      else if has "Human" && has "Soldier" then some .humanSoldier
      else if has "Soldier" && leftoverIsColor p .white then some .soldier11white
      else if has "Elf" then some .elf
      else if has "Squirrel" then some .squirrel11green
      else if has "Insect" then some .insect11green
      else if p.name == "Moloid" then some .moloid
      else none
    | some 3, some 2 =>
      if has "Hero" && p.keywords.vigilance && leftoverIsColor p .white then
        some .hero32vigilance
      else none
    | some 2, some 1 =>
      if has "Villain" && p.keywords.menace && leftoverIsColor p .black then
        some .villain21menace
      else none
    | some 4, some 4 =>
      if has "Bird" && has "Soldier" && p.keywords.flying then some .birdSoldier
      else none
    | some 3, some 1 =>
      if has "Wall" && p.keywords.defender then some .wall
      else none
    | some 6, some 6 =>
      if has "Dragon" && p.keywords.flying then some .dragon
      else none
    | some 6, some 5 =>
      if p.keywords.hexproof then some .leviathan65hexproof
      else none
    | some 0, some 4 =>
      if has "Wall" && p.keywords.defender then some .wall04defender
      else none
    | some 3, some 3 =>
      if p.name == "Doombot" || (has "Robot" && has "Villain") then some .doombot
      else none
    | _, _ => none
  else none

/-- `createTokens` for this controller, with a known token kind. -/
def leftoverCreateTokensKindN? : CardAction → Option (TokenKind × Nat)
  | .createTokens who n parts [] =>
    if leftoverYou who then
      match leftoverTokenKind? parts, valToNat? n with
      | some k, some n => some (k, n)
      | _, _ => none
    else none
  | _ => none

/-- Create `n` Spirit tokens, tapped, optionally also attacking. -/
def leftoverCreateTappedSpirits (n : Nat) (attacking : Bool) : CardAction → Bool
  | .createTokens who k parts states =>
    leftoverYou who && valToNat? k == some n && leftoverTokenKind? parts == some .spirit &&
      (if attacking then leftoverTappedAndAttacking states
       else leftoverTappedOnly states)
  | _ => false

/-- If the equipped creature is legendary, create tapped-and-attacking
Spirits; otherwise create tapped Spirits. -/
def leftoverIfElseCreateSpiritsForEquipped? : CardAction → Bool
  | .ifElse cond [th] [el] =>
    leftoverHostIsLegendary cond &&
      leftoverCreateTappedSpirits 2 true th &&
      leftoverCreateTappedSpirits 2 false el
  | _ => false

/-- Create tokens, then creatures you control get +P/+T. -/
def leftoverCreateThenTeamPump? : CardAction → Option Effect
  | .sequence [.createTokens who n parts [], .continuous effects _] =>
    match leftoverTokenKind? parts, valToNat? n, ContinuousEffect.addedPT? effects,
        ContinuousEffect.massSelector? effects with
    | some kind, some n, some (p, t), some among =>
      if leftoverYou who && among.shape.sameController &&
          among.shape.types.eqTypes [.creature] then
        some (Effect.createTokensThenTeamPump kind n p t)
      else none
    | _, _, _, _ => none
  | _ => none

/-- Grant “whenever this deals combat damage to a player, create a Treasure”. -/
def leftoverGrantCombatDamageCreateTreasure? : List ContinuousEffect → Bool
  | [.gainAbility sel (.triggered (.combatDamage who dest) action)] =>
    (who == .this || who == .source .this) && dest == .player &&
      sel.toTargetKind == .creature &&
      leftoverCreateTokensKindN? action == some (.treasure, 1)
  | _ => false

/-- Creatures you control gain keywords until end of turn. -/
def leftoverTeamGain? (effects : List ContinuousEffect) : Option Keywords :=
  match ContinuousEffect.massSelector? effects with
  | some among =>
    let kws := grantedKeywords effects
    if among.shape.sameController && among.shape.types.eqTypes [.creature] &&
        kws != Keywords.none then
      some kws
    else none
  | none => none

/-- Matching subtypes you control gain menace until end of turn. -/
def leftoverSubtypesGainMenace? (effects : List ContinuousEffect) :
    Option (Array String) :=
  match ContinuousEffect.massSelector? effects with
  | some among =>
    let kws := grantedKeywords effects
    let sts := among.includedSubtypes
    if among.shape.sameController && kws.menace &&
        kws == Keyword.menace.toKeywords && !sts.isEmpty then
      some sts.toArray
    else none
  | none => none

/-- Choose: +1/+1 on a Wolf you control, or create a Treasure. -/
def leftoverWolfPlusOneOrTreasure? : List CardAction → Bool
  | [a, b] =>
    let plusWolf (x : CardAction) : Bool :=
      match x with
      | .putCounter sel .plusOnePlusOne 1 =>
        let s := sel.targetingShape
        s.sameController && s.subtype == some "Wolf"
      | _ => false
    let treasure (x : CardAction) : Bool :=
      leftoverCreateTokensKindN? x == some (.treasure, 1)
    (plusWolf a && treasure b) || (plusWolf b && treasure a)
  | _ => false

/-- Choose: create a Food or a Treasure. -/
def leftoverCreateFoodOrTreasure? : List CardAction → Bool
  | [a, b] =>
    let kind (x : CardAction) : Option TokenKind :=
      match leftoverCreateTokensKindN? x with
      | some (k, 1) => some k
      | _ => none
    match kind a, kind b with
    | some .food, some .treasure | some .treasure, some .food => true
    | _, _ => false
  | _ => false

/-- Sacrifice another creature or artifact the player chooses. -/
def leftoverSacrificeAnotherCreatureOrArtifact? : Selector → Bool
  | .selected _ (.range 1 1) among =>
    among.shape.other && among.shape.sameController &&
      (among.shape.types.eqTypes [.creature, .artifact] ||
        among.shape.types.eqTypes [.artifact, .creature])
  | _ => false

/-- You may sacrifice another creature or artifact. If you do, draw and
create a Treasure. -/
def leftoverMaySacDrawTreasure? : CardAction → Bool
  | .sequence [
      .optional (.controller .this) (.actionId id (.sacrifice sel)),
      .if (.happened (.actionWithId id') _)
        [.draw _ 1, .createTokens who 1 parts []]
    ] =>
    id == id' && leftoverSacrificeAnotherCreatureOrArtifact? sel &&
      leftoverYou who && leftoverTokenKind? parts == some .treasure
  | .sequence [
      .optional (.controller .this) (.actionId id (.sacrifice sel)),
      .if (.happened (.actionWithId id') _)
        [.createTokens who 1 parts [], .draw _ 1]
    ] =>
    id == id' && leftoverSacrificeAnotherCreatureOrArtifact? sel &&
      leftoverYou who && leftoverTokenKind? parts == some .treasure
  | _ => false

/-- Creature cards in this object's controller's graveyard. -/
def leftoverYourGyCreatures? : Selector → Bool
  | .intersection fs =>
    fs.any (fun s => s == .zone .graveyard) &&
      fs.any (fun
        | .cardType .creature => true
        | _ => false) &&
      fs.any (fun
        | .owner (.controller .this) => true
        | _ => false)
  | _ => false

/-- Return a targeted permanent card from your graveyard that was put
there this turn. -/
def leftoverEnterReturnGyPermanentThisTurn? : CardAction → Bool
  | .returnToHand sel =>
    match sel.among? with
    | some among =>
      among.includesInGraveyard && among.shape.mustBePermanent &&
        among.wasObjectOfPutToGraveyardThisTurn?
    | none => false
  | _ => false

/-- Return target creature card from your graveyard to your hand. -/
def leftoverEnterReturnCreatureFromGyToHand? : CardAction → Bool
  | .returnToHand (.target _ among) => leftoverYourGyCreatures? among
  | _ => false

/-- Return up to one targeted nonland, nontoken permanent. -/
def leftoverEnterReturnNonlandNontoken? : CardAction → Bool
  | .returnToHand (.targets _ (.range 0 1) among) =>
    among.shape.nonland && among.shape.nontoken
  | _ => false

/-- This fights up to one other target creature. -/
def leftoverEnterFightUpToOne? : CardAction → Bool
  | .fight src dest =>
    (src == .this || src == .source .this) &&
      match dest with
      | .targets _ (.range 0 1) among =>
        among.shape.other && among.shape.types.eqTypes [.creature]
      | _ => false
  | _ => false

/-- You may sacrifice another creature. When you do, destroy target
nonland permanent an opponent controls. -/
def leftoverEnterMaySacAnotherThenDestroyOppNonland? : CardAction → Bool
  | .sequence [
      .optional (.controller .this) (.actionId id (.sacrifice (.selected _ (.range 1 1) among))),
      .if (.happened (.actionWithId id') _) [.destroy sel]
    ] =>
    id == id' && among.shape.other && among.shape.sameController &&
      among.shape.types.eqTypes [.creature] &&
      sel.targetingShape.nonland && sel.targetingShape.opponentControls
  | _ => false

/-- +1/+1 on each other creature you control; you gain 1 life for each of
those creatures. -/
def leftoverPlusOneEachOtherGainLife? : CardAction → Bool
  | .sequence [
      .putCounter sel .plusOnePlusOne 1,
      .forEachVariable _ among [.gainLife who 1]
    ]
  | .sequence [
      .forEachVariable _ among [.gainLife who 1],
      .putCounter sel .plusOnePlusOne 1
    ] =>
    leftoverYou who &&
      sel.shape.anotherCreatureYouControl &&
      among.shape.anotherCreatureYouControl
  | _ => false

/-- Target attacking creature gains flying. -/
def leftoverGrantFlyingToAttacking? : CardAction → Bool
  | .continuous effects _ =>
    let kws := grantedKeywords effects
    kws.flying &&
      match ContinuousEffect.targetingSelector? effects with
      | some sel => sel.targetingShape.attackingCreature
      | none => false
  | _ => false

/-- Those creatures (targets of this spell) gain flying. -/
def leftoverGrantFlyingToThose? : List ContinuousEffect → Bool
  | [.gainAbility who (.keyword .flying)] =>
    who.leftoverIsTargetOfThisSpell? &&
      who.shape.mustBePermanent &&
      who.shape.types.eqTypes [.creature]
  | _ => false

/-- This mode has not been chosen this turn by any player. -/
def leftoverModeUnchosenThisTurn? (id : Nat) : Condition → Bool
  | .not (.happened (.modeWithIdChosen chooser id') .turnStart) =>
    chooser == .player && id == id'
  | _ => false

/-- Alliance modes: add {G}{G}{G}; +1/+1 on each creature you control;
scry 2, then draw. Each mode must be unchosen this turn. -/
def leftoverAllianceModes? (who : Selector) :
    List (Nat × Condition × List CardAction) → Bool
  | [
      (id1, c1, [.addMana gainer [.mono .green, .mono .green, .mono .green]]),
      (id2, c2, [.putCounter sel .plusOnePlusOne 1]),
      (id3, c3, [.sequence [.scry _ 2, .draw _ 1]])
    ] =>
    leftoverYou who && leftoverYou gainer &&
      id1 != id2 && id2 != id3 && id1 != id3 &&
      leftoverModeUnchosenThisTurn? id1 c1 &&
      leftoverModeUnchosenThisTurn? id2 c2 &&
      leftoverModeUnchosenThisTurn? id3 c3 &&
      sel.shape.sameController &&
      sel.shape.types.eqTypes [.creature]
  | _ => false

/-- Target creature or land. -/
def leftoverCreatureOrLandTarget? (s : Selector) : Bool :=
  s.targetingShape.types.eqTypes [.creature, .land]

/-- Exile an argument of this triggered ability from a graveyard, then you
may play it until the end of your next turn. -/
def leftoverExileGyPlayUntilNextTurn? : CardAction → Bool
  | .optional (.controller .this)
      (.sequence [
        .actionId id (.exile among),
        .continuous [.canPlay permit (.wasCreatedByAction created)] duration
      ]) =>
    id == created && leftoverYou permit &&
      among.includesInGraveyard && among.includesWasArgumentOfTrigger &&
      leftoverUntilEndOfYourNextTurn? duration
  | _ => false

/-- Copy that spell or ability; you may choose new targets. -/
def leftoverCopyWithNewTargets? : CardAction → Bool
  | .copyWithNewTargets who what =>
    leftoverYou who && what.includesWasArgumentOfTrigger
  | _ => false

/-- Sacrifice an artifact or discard a nonland card. -/
def leftoverSacrificeArtifactOrDiscardNonlandCost? : List Cost → Bool
  | [] => false
  | .or cs :: rest =>
    let sacArt :=
      cs.any fun
        | .sacrificeCount s 1 => s.shape.types.eqTypes [.artifact]
        | .sacrifice s => s.shape.types.eqTypes [.artifact]
        | _ => false
    let discNonland :=
      cs.any fun
        | .discard s => s.shape.nonland
        | _ => false
    (sacArt && discNonland) || leftoverSacrificeArtifactOrDiscardNonlandCost? rest
  | _ :: rest => leftoverSacrificeArtifactOrDiscardNonlandCost? rest

/-- You may sacrifice an artifact or discard a nonland card. If you do,
deal 2 damage to any target. -/
def leftoverEnterMaySacOrDiscardNonlandThenDamage? : CardAction → Bool
  | .optionalPayFor who costs [.dealDamage _ dest (.int 2)] =>
    leftoverYou who &&
      leftoverSacrificeArtifactOrDiscardNonlandCost? costs &&
      Selector.leftoverAnyTarget? dest
  | _ => false

/-- Source gets +1/+1 until end of turn for each other creature you control. -/
def leftoverPumpForEachOtherCreature? : List ContinuousEffect → Bool
  | [.addPower who (Value.count among),
     .addToughness who' (Value.count among')] =>
    who == who' &&
      (who == .source .this || who == .this) &&
      among == among' &&
      among.shape.anotherCreatureYouControl
  | _ => false

/-- Other permanents you control of a subtype get +1/+0 for each artifact
token you control. Power is the count. Zero toughness is omitted. -/
def leftoverOtherSubtypeGetPowerPerArtifactToken?
    (power : ContinuousEffect) : Option String :=
  match power with
  | .addPower who (Value.count among) =>
    if among.shape.token && among.shape.sameController &&
        among.shape.types.eqTypes [.artifact] then
      who.shape.anotherSubtypeYouControl
    else none
  | _ => none

/-- You may pay {1}. If you do, target creature with haste can't be
blocked this turn except by creatures with haste. -/
def leftoverMayPayHasteUnblockable? : CardAction → Bool
  | .optionalPayFor who [.mana [.generic 1]] [.continuous effects _] =>
    leftoverYou who &&
      match effects with
      | [.forbid (.block (.not (.keyword .haste)) dest)] =>
        dest.targetingShape.types.eqTypes [.creature]
      | _ => false
  | _ => false

/-- Cards in this object's controller's graveyard, with no further filter. -/
def leftoverYourGraveyardCards? : Selector → Bool
  | .intersection fs =>
    fs.length == 2 &&
      fs.any (· == .zone .graveyard) &&
      fs.any (· == .owner (.controller .this))
  | _ => false

/-- +P/+T on this while your graveyard has at least seven cards. -/
def leftoverThresholdGets?
    (among : Selector) (inners : List ContinuousEffect) : Option StaticAbility :=
  if leftoverYourGraveyardCards? among then
    match ContinuousEffect.addedPT? inners with
    | some (p, t) =>
      let onThis :=
        inners.all fun e =>
          match e with
          | .addPower who _ | .addToughness who _ => isThisOrItsSource who
          | _ => false
      if onThis && (p != 0 || t != 0) then some (.thresholdGets p t) else none
    | none => none
  else none

/-- +P/+T on this as long as your graveyard has creature cards. With
`gainAllSubtypes` of creature, also all creature types. -/
def leftoverGetsIfGyCreatureCards?
    (among : Selector) (inners : List ContinuousEffect) : Option StaticAbility :=
  if leftoverYourGyCreatures? among then
    let ptEffects :=
      inners.filter fun e =>
        match e with
        | .addPower _ _ | .addToughness _ _ => true
        | _ => false
    let rest :=
      inners.filter fun e =>
        match e with
        | .addPower _ _ | .addToughness _ _ => false
        | _ => true
    let onThis := ptEffects.all fun e => leftoverThis e.selector
    match ContinuousEffect.foundAddedPT? ptEffects, rest with
    | some (p, t), [] =>
      if onThis then some (.getsIfGyCreatureCards 2 p t) else none
    | some (p, t), [.gainAllSubtypes typesWho .creature] =>
      if onThis && leftoverThis typesWho then
        some (.getsAndAllTypesIfGyCreatureCards 2 p t)
      else none
    | _, _ => none
  else none

/-- Target opponent as a numbered target. -/
def leftoverTargetOpponent? : Selector → Bool
  | .target _ (.opponent _) => true
  | _ => false

/-- Target player as a numbered target. -/
def leftoverTargetPlayer? : Selector → Bool
  | .target _ .player => true
  | _ => false

/-- Objects milled by the numbered action that also match `pred`. -/
def leftoverMilledBy (id : Nat) (pred : Selector → Bool) : Selector → Bool
  | .intersection fs =>
    fs.any (fun s => s == .wasObjectOfAction id) && fs.any pred
  | _ => false

/-- Instant or sorcery cards. -/
def leftoverInstantOrSorceryFilter : Selector → Bool
  | s => s.shape.types.eqTypes [.instant, .sorcery]

/-- Land cards. -/
def leftoverLandFilter : Selector → Bool
  | s => s == .cardType .land || s.shape.types.eqTypes [.land]

/-- A permanent card (among milled cards). -/
def leftoverPermanentCardFilter : Selector → Bool
  | .zone .battlefield => true
  | _ => false

/-- A subtype card or an enchantment card. -/
def leftoverSubtypeOrEnchantment? : Selector → Option String
  | .union fs =>
    if fs.any (fun s => s == .cardType .enchantment) then
      fs.findSome? fun s =>
        match s with
        | .subtype st => some st.toString
        | _ => none
    else none
  | _ => none

/-- The printed subtype among milled cards, if that is the only filter. -/
def leftoverMilledSubtype? (id : Nat) : Selector → Option String
  | .intersection fs =>
    if fs.any (fun s => s == .wasObjectOfAction id) then
      fs.findSome? fun s =>
        match s with
        | .subtype st => some st.toString
        | _ => none
    else none
  | _ => none

/-- Chosen cards from among those milled by `id`. -/
def leftoverSelectedMilled? (id : Nat) (pred : Selector → Bool) :
    Selector → Option (Nat × Nat)
  | .selected _ (.range (.int (.ofNat lo)) (.int (.ofNat hi))) among =>
    if leftoverMilledBy id pred among then some (lo, hi) else none
  | .targets _ (.range (.int (.ofNat lo)) (.int (.ofNat hi))) among =>
    if leftoverMilledBy id pred among then some (lo, hi) else none
  | _ => none

/-- Mill n, then put an instant or sorcery card from among them into hand. -/
def leftoverMillThenPutInstantOrSorcery? : CardAction → Option Nat
  | .sequence [.actionId id (.mill who (.int (.ofNat n))), .returnToHand sel] =>
    match leftoverSelectedMilled? id leftoverInstantOrSorceryFilter sel with
    | some (lo, 1) =>
      if leftoverYou who && lo ≤ 1 then some n else none
    | _ => none
  | _ => none

/-- Mill n, then put up to `max` land cards from among them into hand. -/
def leftoverMillThenPutLands? : CardAction → Option (Nat × Nat)
  | .sequence [.actionId id (.mill who (.int (.ofNat n))), .returnToHand sel] =>
    match leftoverSelectedMilled? id leftoverLandFilter sel with
    | some (0, max) =>
      if leftoverYou who then some (n, max) else none
    | _ => none
  | _ => none

/-- Mill n, then put all instant and sorcery cards from among them into hand. -/
def leftoverMillThenPutAllInstantsOrSorceries? : CardAction → Option Nat
  | .sequence [.actionId id (.mill who (.int (.ofNat n))), .returnToHand among] =>
    if leftoverYou who && leftoverMilledBy id leftoverInstantOrSorceryFilter among then
      some n
    else none
  | _ => none

/-- Mill n, you may put a permanent card from among them into hand, gain life. -/
def leftoverMillThenPutPermanentGainLife? : CardAction → Option (Nat × Nat)
  | .sequence [
      .actionId id (.mill who (.int (.ofNat n))),
      .optional (.controller .this) (.returnToHand sel),
      .gainLife gainer (.int (.ofNat life))
    ] =>
    match leftoverSelectedMilled? id leftoverPermanentCardFilter sel with
    | some (lo, 1) =>
      if leftoverYou who && leftoverYou gainer && lo ≤ 1 then some (n, life) else none
    | _ => none
  | _ => none

/-- Mill n, you may put a subtype or enchantment card from among them into hand. -/
def leftoverMillThenPutSubtypeOrEnchantment? : CardAction → Option (Nat × String)
  | .sequence [
      .actionId id (.mill who (.int (.ofNat n))),
      .optional (.controller .this) (.returnToHand (.selected _ (.range (.int (.ofNat lo)) 1) among))
    ] =>
    if leftoverYou who && lo ≤ 1 then
      match among with
      | .intersection fs =>
        if fs.any (fun s => s == .wasObjectOfAction id) then
          fs.findSome? leftoverSubtypeOrEnchantment? |>.map (fun st => (n, st))
        else none
      | _ => none
    else none
  | .sequence [
      .actionId id (.mill who (.int (.ofNat n))),
      .optional (.controller .this) (.returnToHand (.targets _ (.range (.int (.ofNat lo)) 1) among))
    ] =>
    if leftoverYou who && lo ≤ 1 then
      match among with
      | .intersection fs =>
        if fs.any (fun s => s == .wasObjectOfAction id) then
          fs.findSome? leftoverSubtypeOrEnchantment? |>.map (fun st => (n, st))
        else none
      | _ => none
    else none
  | _ => none

end CardAction

end Mtg.Engine
