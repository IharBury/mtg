import Mtg.Engine.Card.Definition.CompiledLeftovers

/-!
# Compiling a card action

`CardAction.compile` reads one printed action into an `Effect`.
`toEffect` is the spell reading and `toAbilityEffect` is the activated
ability reading.
-/

namespace Mtg.Engine

namespace CardAction

/-- Compile `continuous` effects, reading targeting from `target`
and mass application from constraint selectors. -/
def compile (action : CardAction) (asAbility : Bool) : Effect :=
  match leftoverSearchBasicBeholdUntap? action with
  | some st => Effect.searchBasicBeholdSubtypeUntap st
  | none =>
  match leftoverCompiled? action with
  | some e => e
  | none =>
  match leftoverSearchLibraryThenShuffle? action with
  | some e => e
  | none =>
  match leftoverPlusOneOnTarget? action with
  | some e => e
  | none =>
  match leftoverUntapPumpAttach? action with
  | some (p, t) => Effect.untapPumpMaybeAttach p t
  | none =>
    if leftoverCreatureYouControlDealsPowerToOppCreature? action then
      Effect.creatureYouControlDealsPowerToOppCreature
    else if leftoverPlusOnePlusOneTrampleHexproof? action then
      Effect.plusOnePlusOneTrampleHexproof
    else
    match leftoverBecomeSubtypeWithLandsPT? action with
    | some subtype => Effect.becomeSubtypeWithLandsPT subtype
    | none =>
    if leftoverCounterExile? action then Effect.counterExilePermanentMayCast
    else if leftoverExileTopPlayUntilEndOfNextTurn? action then
      Effect.exileTopPlayUntilEndOfNextTurn
    else if leftoverEquipAttach? action then Effect.attachToTargetCreatureYouControl
    else
      match leftoverDrawDiscard? action with
      | some n =>
        if asAbility then Effect.abilityDrawThenDiscard n
        else Effect.drawThenDiscard n
      | none =>
        match leftoverPlusOneAndGainLife? action with
        | some n => Effect.plusOneUpToOneAndPlayerGainsLife n
        | none =>
          match leftoverPumpAndExileIfDies? action with
          | some (p, t) => Effect.pumpAndExileIfDies p t
          | none =>
            match leftoverPumpAndLifelink? action with
            | some (p, t) => Effect.pumpAndLifelink p t
            | none =>
              match leftoverPumpAndGrantKeywords? action with
              | some (p, t, k) =>
                if asAbility then
                  match action with
                  | .continuous effects _ =>
                    match ContinuousEffect.targetingSelector? effects with
                    | some sel =>
                      if sel.targetingShape.anotherCreatureYouControl then
                        Effect.anotherYouControlGetsAndGrant p t k
                      else Effect.pumpAndGrantKeywords p t k
                    | none => Effect.pumpAndGrantKeywords p t k
                  | _ => Effect.pumpAndGrantKeywords p t k
                else Effect.pumpAndGrantKeywords p t k
              | none =>
              match leftoverPumpThenDraw? action with
              | some (p, t) => Effect.pumpThenDraw p t
              | none =>
              match leftoverCreaturesTargetPlayerGet? action with
              | some (p, t) => Effect.creaturesTargetPlayerGet p t
              | none =>
              match leftoverAllCreaturesGet? action with
              | some (p, t) => Effect.allCreaturesGet p t
              | none =>
              if leftoverTargetCantBeBlocked? action then
                Effect.targetCantBeBlockedThisTurn
              else
                match leftoverDrawLoseLifeSelf? action with
                | some (cards, life) => Effect.drawAndLoseLife cards life
                | none =>
                match leftoverTargetPlayerDrawLoseLife? action with
                | some (cards, life) => Effect.targetPlayerDrawLoseLife cards life
                | none =>
                  match action with
                  | .continuous effects _duration => compileContinuous effects asAbility
                  | .tap s => compileTap s asAbility
                  | .untap s => compileUntap s asAbility
                  | .dealDamage _source victim (.int n) =>
                    if n >= 0 then compileDamage victim n.toNat asAbility
                    else continuousEffect none [] asAbility
                  | .dealDamage _ _ _ =>
                    continuousEffect none [] asAbility
                  | .divideDamage _who _source victim n =>
                    match valToNat? n with
                    | some n => compileDamage victim n asAbility
                    | none => continuousEffect none [] asAbility
                  | .draw who n =>
                    match valToNat? n with
                    | some n =>
                      if asAbility && who.among? == some .player then
                        Effect.abilityTargetPlayerDraw n
                      else if asAbility then Effect.abilityDraw n
                      else Effect.draw n
                    | none => continuousEffect none [] asAbility
                  | .scry _who n =>
                    match valToNat? n with
                    | some n => if asAbility then Effect.abilityScry n else Effect.scry n
                    | none => continuousEffect none [] asAbility
                  | .sequence (a :: _) => compile a asAbility
                  | .sequence [] => continuousEffect none [] asAbility
                  | .if _ (a :: _) => compile a asAbility
                  | .if _ [] => continuousEffect none [] asAbility
                  | .ifElse _ (a :: _) _ => compile a asAbility
                  | .ifElse _ [] (a :: _) => compile a asAbility
                  | .ifElse _ [] [] => continuousEffect none [] asAbility
                  | .optional _ inner => compile inner asAbility
                  | .attach _ _ => Effect.untapPumpMaybeAttach 0 0
                  | .chooseUniqueModes _ (a :: _) => compile a asAbility
                  | .chooseUniqueModes _ [] => continuousEffect none [] asAbility
                  | .chooseModeRestricted _ ((_, _, a :: _) :: _) =>
                    compile a asAbility
                  | .chooseModeRestricted _ _ =>
                    continuousEffect none [] asAbility
                  | .counter _ => Effect.counterSpell
                  | .preventable _ costs (.counter _) =>
                    Effect.counterUnlessPays (ManaCost.manaValue (Cost.manaCost costs))
                  | .preventable _ _ inner => compile inner asAbility
                  | .optionalPayFor _ _ (a :: _) => compile a asAbility
                  | .optionalPayFor _ _ [] => continuousEffect none [] asAbility
                  | .discard _ n =>
                    match valToNat? n with
                    | some n => Effect.drawThenDiscard n
                    | none => continuousEffect none [] asAbility
                  | .putCounter (.source .this) .plusOnePlusOne (.int (.ofNat n)) =>
                    Effect.putPlusOnePlusOneOnSource n
                  | .putCounter (.source .this) .plusOnePlusOne .x =>
                    Effect.plusOneX
                  | .putCounter _ _ _ => continuousEffect none [] asAbility
                  | .removeCounter _ _ _ | .removeAllCounters _ =>
                    continuousEffect none [] asAbility
                  | .exile _ | .exileFaceDown _ =>
                    continuousEffect none [] asAbility
                  | .exchangeControl _ => Effect.exchangeControlSharingType
                  | .destroy s =>
                    if s.toTargetKind == .creatureWithFlying then
                      Effect.destroyCreatureWithFlying
                    else if asAbility && s.toTargetKind == .noncreatureArtifactOrEnchantment then
                      Effect.destroyTargetNoncreatureArtOrEnch
                    else if asAbility && s.toTargetKind == .artifactOrEnchantment then
                      Effect.destroyTargetArtifactOrEnchantment
                    else if asAbility && s.toTargetKind == .permanent then
                      Effect.destroyTargetPermanent
                    else
                      match s.toTargetKind with
                      | .creaturePowerAtLeast n => Effect.destroyCreaturePowerAtLeast n
                      | _ => Effect.destroyCreature
                  | .gainLife _ n =>
                    match valToNat? n with
                    | some n => Effect.gainLife n
                    | none => continuousEffect none [] asAbility
                  | .playerSelectAction _ _ actions =>
                    match actions with
                    | [.putOnTopOfLibrary _, .putOnBottomOfLibrary _] =>
                      Effect.putOnTopOrBottom
                    | a :: _ => compile a asAbility
                    | [] => continuousEffect none [] asAbility
                  | .putOnTopOfLibrary _ => Effect.putOnTopOrBottom
                  | .putOnBottomOfLibrary _ => Effect.putOnTopOrBottom
                  | .putIntoLibraryFromTop _ 1 => Effect.putOnTopOrBottom
                  | .putIntoLibraryFromTop _ _ =>
                    continuousEffect none [] asAbility
                  | .actionId _ inner => compile inner asAbility
                  | .defineValueVariable _ _ => continuousEffect none [] asAbility
                  | .loseLife _ _ => continuousEffect none [] asAbility
                  | .sacrifice _ => continuousEffect none [] asAbility
                  | .returnToHand _ => Effect.returnFromGraveyardToHand
                  | .putOntoBattlefield _ => continuousEffect none [] asAbility
                  | .putOntoBattlefieldInState _ _ => continuousEffect none [] asAbility
                  | .searchLibraryThenShuffle _ _ =>
                    continuousEffect none [] asAbility
                  | .holdOutInLibrary _ => continuousEffect none [] asAbility
                  | .defineSelectorVariable _ _ => continuousEffect none [] asAbility
                  | .forEachVariable _ _ _ => continuousEffect none [] asAbility
                  | .reveal _ => continuousEffect none [] asAbility
                  | .fight _ _ =>
                    continuousEffect none [] asAbility
                  | .addManaOfOneColor who syms n =>
                    if leftoverAddAnyColor? (.addManaOfOneColor who syms n) then
                      Effect.addAnyColor
                    else
                      continuousEffect none [] asAbility
                  | .addManaInAnyCombination who syms n =>
                    if who == .controller .this && syms == ManaSymbol.anyColor &&
                        n == 4 then
                      Effect.addFourAnyCombination
                    else
                      continuousEffect none [] asAbility
                  | .addMana _ syms =>
                    match addedManaTypes? syms with
                    | some types => Effect.addMana types
                    | none => continuousEffect none [] asAbility
                  | .keyword who k =>
                    match leftoverKeywordAction? k with
                    | some e =>
                      match k with
                      | .connive (.int 1) | .harness =>
                        let ok :=
                          if asAbility then leftoverSourceThis who else leftoverThis who
                        if ok then e else continuousEffect none [] asAbility
                      | _ => e
                    | none => continuousEffect none [] asAbility
                  | .createTokens _ .x parts [] =>
                    match leftoverTokenKind? parts with
                    | some kind =>
                      if asAbility then Effect.abilityCreateTokensX kind
                      else Effect.createTokensX kind
                    | none => continuousEffect none [] asAbility
                  | .modifyReplacementCreatedTokenCount _
                  | .duplicateReplacingTrigger _ =>
                    continuousEffect none [] asAbility
                  | .createTokens _ n parts states =>
                    match leftoverTokenKind? parts, valToNat? n with
                    | some kind, some n =>
                      if states == [] then
                        if asAbility then Effect.abilityCreateTokens kind n
                        else Effect.createTokens kind n
                      else if leftoverTappedOnly states then
                        Effect.createTappedTokens kind n
                      else continuousEffect none [] asAbility
                    | _, _ => continuousEffect none [] asAbility
                  | .mill who n =>
                    match valToNat? n with
                    | some n =>
                      if leftoverTargetPlayer? who then Effect.millPlayer n
                      else continuousEffect none [] asAbility
                    | none => continuousEffect none [] asAbility
                  | .surveil who n =>
                    match valToNat? n with
                    | some n =>
                      if leftoverYou who then Effect.scry n
                      else continuousEffect none [] asAbility
                    | none => continuousEffect none [] asAbility
                  | .copyWithNewTargets _ _ =>
                    continuousEffect none [] asAbility
                  | .keepReplacedAction | .healAllDamage _ =>
                    continuousEffect none [] asAbility
                  | .shuffleIntoOwnersLibrary _ | .lookAt _
                  | .putOnLibraryBottomInRandomOrder _ | .chooseCreatureType _
                  | .mayCast _ _ | .reflexive _ _ | .delayedTrigger _ _
                  | .exileUntil _ _
                  | .addPhaseAfterThisPhase _ | .chooseOddEven _ _ =>
                    continuousEffect none [] asAbility

/-- If a creature an opponent controls would die, exile it instead and
create a 2/2 green Wolf when you do. -/
def exileOppDeathCreateWolf? (who : Selector) (actions : List CardAction) : Bool :=
  who == .intersection [
    .zone .battlefield, .cardType .creature,
    .controlled (.opponent (.controller .this))] &&
    match actions with
    | [.actionId id (.exile .replacingObject), .reflexive id' [wolf]] =>
      id == id' && leftoverCreateTokensKindN? wolf == some (.wolf, 1)
    | _ => false

/-- “Choose one or both”: one or two distinct modes (CR 700.2). -/
def isChooseOneOrBoth : CardAction → Bool
  | .chooseUniqueModes r _ => r == .range 1 2
  | _ => false

/-- Modes of a “Choose one” or “Choose one or both” action. -/
def leftoverModes? : CardAction → Option (Array Effect)
  | .chooseUniqueModes _ as =>
    some ((as.map fun a => compile a false).toArray)
  | .chooseModeRestricted _ modes =>
    some ((modes.map fun (_, _, as) => compile (.sequence as) false).toArray)
  | _ => none

/-- Compile to a spell-shaped `Effect`. -/
def toEffect (action : CardAction) : Effect :=
  compile action false

/-- Compile to an activated-ability `Effect`. -/
def toAbilityEffect (action : CardAction) : Effect :=
  compile action true

/-- The number of Treasure artifacts this object's controller controls. -/
def isTreasuresYouControlCount : Value → Bool
  | .count among =>
    let s := among.shape
    s.mustBePermanent && s.sameController && !s.other && !s.opponentControls &&
      !s.flying && !s.attacking && !s.token && !s.nontoken &&
      s.subtype == some "Treasure" && s.types.eqTypes [.artifact] &&
      s.powerAtLeast.isNone && s.powerAtMost.isNone && !s.hasPlusOneCounter
  | _ => false

/-- Damage to any target equal to the number of Treasures you control. -/
def leftoverDamageEqualTreasures? : CardAction → Bool
  | .dealDamage src victim amount =>
    (src == .this || src == .source .this) &&
      Selector.leftoverAnyTarget? victim &&
      isTreasuresYouControlCount amount
  | _ => false

/-- Deal damage to any target, then destroy the object of that action if
that damage was dealt to it and it has this subtype. -/
def leftoverDealDamageDestroyIfSubtype? : CardAction → Option (Nat × String)
  | .sequence [
      .actionId id (.dealDamage src victim (.int (.ofNat n))),
      .if (.anySubtype (.wasObjectOfAction id') st)
        [.destroy (.wasObjectOfAction id'')]
    ] =>
    if n != 0 && id == id' && id == id'' &&
        (src == .this || src == .source .this) &&
        Selector.leftoverAnyTarget? victim then
      some (n, st.toString)
    else none
  | _ => none

end CardAction

end Mtg.Engine
