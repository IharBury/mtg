import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.ChapterEffects
import Mtg.Engine.Card.OracleNorm
import Mtg.Engine.Card.TriggeredAbility

/-!
Argument values in modeled Oracle text.

A candidate ability is a shape. `Nat`, `Int`, and `String` arguments are read
back out of the printed line, so a prototype such as `Effect.draw 1` also
matches “Draw seven cards.”
-/

namespace Mtg.Engine.OracleArgs

open OracleNorm

/-- One printed argument. -/
inductive SlotVal where
  | nat (n : Nat)
  | int (i : Int)
  | str (s : String)
  deriving BEq, Repr, Inhabited

inductive NatFmt where
  | digits
  | cards
  | counters
  | brace
  | english
  deriving BEq, Repr

inductive IntFmt where
  | signed
  | digits
  deriving BEq, Repr

inductive StrFmt where
  | word (n : Nat)
  | plural
  | cycling (n : Nat)
  | non
  deriving BEq, Repr

/-- One token of a normalized Oracle line. A hole remembers which argument it is. -/
inductive Pat where
  | lit (s : String)
  | nat (i : Nat) (fmt : NatFmt)
  | int (i : Nat) (fmt : IntFmt)
  | str (i : Nat) (fmt : StrFmt)
  | pt (i j : Nat) (signed : Bool)
  deriving BEq, Repr

inductive Mode where
  | collect
  | fill
  deriving BEq

structure St where
  mode : Mode
  vals : List SlotVal

abbrev ArgM := StateM St

def tokenize (s : String) : List String :=
  s.splitOn " " |>.filter (· != "")

def capFirst (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: rest => String.ofList (c.toUpper :: rest)

def tokenChar (c : Char) : Bool :=
  c.isAlphanum || c == '+' || c == '/' || c == '-' || c == '{' || c == '}' || c == '\''

def takeNat (n : Nat) : ArgM Nat := do
  let s ← get
  match s.mode with
  | .collect =>
    set { s with vals := .nat n :: s.vals }
    return n
  | .fill =>
    match s.vals with
    | .nat v :: rest =>
      set { s with vals := rest }
      return v
    | _ => return n

def takeInt (i : Int) : ArgM Int := do
  let s ← get
  match s.mode with
  | .collect =>
    set { s with vals := .int i :: s.vals }
    return i
  | .fill =>
    match s.vals with
    | .int v :: rest =>
      set { s with vals := rest }
      return v
    | _ => return i

def takeStr (str : String) : ArgM String := do
  let s ← get
  match s.mode with
  | .collect =>
    set { s with vals := .str str :: s.vals }
    return str
  | .fill =>
    match s.vals with
    | .str v :: rest =>
      set { s with vals := rest }
      return v
    | _ => return str

def takeOptNat (o : Option Nat) : ArgM (Option Nat) :=
  match o with
  | none => pure none
  | some n => return some (← takeNat n)

def takeOptInt (o : Option Int) : ArgM (Option Int) :=
  match o with
  | none => pure none
  | some i => return some (← takeInt i)

def takeOptStr (o : Option String) : ArgM (Option String) :=
  match o with
  | none => pure none
  | some str => return some (← takeStr str)

def takeStrs (xs : Array String) : ArgM (Array String) :=
  xs.mapM takeStr

def takeSymbol (s : ManaSymbol) : ArgM ManaSymbol :=
  match s with
  | .generic n => return .generic (← takeNat n)
  | s => return s

def takeCost (c : ManaCost) : ArgM ManaCost := do
  return { symbols := ← c.symbols.mapM takeSymbol }

def takeKind (k : EffectTargetKind) : ArgM EffectTargetKind := do
  match k with
  | .creatureYouControlSubtype s => return .creatureYouControlSubtype (← takeStr s)
  | .creatureSpellPTAtMost n => return .creatureSpellPTAtMost (← takeNat n)
  | .creaturePowerAtLeast n => return .creaturePowerAtLeast (← takeInt n)
  | .creaturePowerAtMost n => return .creaturePowerAtMost (← takeInt n)
  | .creatureYouControlAnySubtype ss => return .creatureYouControlAnySubtype (← takeStrs ss)
  | .creatureCardInYourGraveyardMvAtMost n =>
    return .creatureCardInYourGraveyardMvAtMost (← takeNat n)
  | .creatureYouControlPowerAtMost n => return .creatureYouControlPowerAtMost (← takeInt n)
  | .creatureMvAtMost n => return .creatureMvAtMost (← takeNat n)
  | .creatureToughnessAtLeast n => return .creatureToughnessAtLeast (← takeInt n)
  | .enchantmentMvAtLeast n => return .enchantmentMvAtLeast (← takeNat n)
  | .oppCreaturePowerAtMost n => return .oppCreaturePowerAtMost (← takeInt n)
  | .upToTwoCreaturesTotalMvAtMost n => return .upToTwoCreaturesTotalMvAtMost (← takeNat n)
  | k => return k

def takeTargeting (t : EffectTargeting) : ArgM EffectTargeting := do
  return { t with kind := ← takeKind t.kind }

def takeAction (a : PermanentAction) : ArgM PermanentAction := do
  match a with
  | .pump p t => return .pump (← takeInt p) (← takeInt t)
  | .pumpAndTrample p t => return .pumpAndTrample (← takeInt p) (← takeInt t)
  | .plusOne n => return .plusOne (← takeNat n)
  | .dealDamage n => return .dealDamage (← takeNat n)
  | .dealDamageLoseIndestructibleExile n =>
    return .dealDamageLoseIndestructibleExile (← takeNat n)
  | .pumpAndLifelink p t => return .pumpAndLifelink (← takeInt p) (← takeInt t)
  | .pumpAndExileIfDies p t => return .pumpAndExileIfDies (← takeInt p) (← takeInt t)
  | .pumpAndGrant p t k => return .pumpAndGrant (← takeInt p) (← takeInt t) k
  | a => return a

def takeSpell (r : SpellResolution) : ArgM SpellResolution := do
  match r with
  | .onPermanent a => return .onPermanent (← takeAction a)
  | .allCreaturesPump p t => return .allCreaturesPump (← takeInt p) (← takeInt t)
  | .drawAndLoseLife cards life => return .drawAndLoseLife (← takeNat cards) (← takeNat life)
  | .playerDrawLoseLife cards life =>
    return .playerDrawLoseLife (← takeNat cards) (← takeNat life)
  | .creaturesOfPlayerPump p t => return .creaturesOfPlayerPump (← takeInt p) (← takeInt t)
  | .destroyAndControllerLosesLife n => return .destroyAndControllerLosesLife (← takeNat n)
  | .draw n => return .draw (← takeNat n)
  | .drawThenDiscard n => return .drawThenDiscard (← takeNat n)
  | .scry n => return .scry (← takeNat n)
  | .tapScryDraw a b => return .tapScryDraw (← takeNat a) (← takeNat b)
  | .counterUnlessPays n => return .counterUnlessPays (← takeNat n)
  | .untapPumpMaybeAttach p t => return .untapPumpMaybeAttach (← takeInt p) (← takeInt t)
  | .plusOneAndPlayerGainsLife n => return .plusOneAndPlayerGainsLife (← takeNat n)
  | .creaturesYouControlPump p t => return .creaturesYouControlPump (← takeInt p) (← takeInt t)
  | .destroyArtifactOrEnchantmentGainLife n =>
    return .destroyArtifactOrEnchantmentGainLife (← takeNat n)
  | .amassGoblins n => return .amassGoblins (← takeNat n)
  | .drawLoseLifeThenAmass n => return .drawLoseLifeThenAmass (← takeNat n)
  | .returnCreatureFromGyThenAmass n => return .returnCreatureFromGyThenAmass (← takeNat n)
  | .counterThenRecruitIfMvAtMost n => return .counterThenRecruitIfMvAtMost (← takeNat n)
  | .plusOneThenFight n => return .plusOneThenFight (← takeNat n)
  | .drawIfFromGy a b => return .drawIfFromGy (← takeNat a) (← takeNat b)
  | .amassGoblinsOrFromGy a b => return .amassGoblinsOrFromGy (← takeNat a) (← takeNat b)
  | .dealDamageToEachOppCreature n => return .dealDamageToEachOppCreature (← takeNat n)
  | .targetPlayerDraw n => return .targetPlayerDraw (← takeNat n)
  | .dealDamageToCreatureExileIfDies n => return .dealDamageToCreatureExileIfDies (← takeNat n)
  | .dealDamageToEachNonDragon n => return .dealDamageToEachNonDragon (← takeNat n)
  | .millThenPutInstantOrSorcery n => return .millThenPutInstantOrSorcery (← takeNat n)
  | .millThenPutLands a b => return .millThenPutLands (← takeNat a) (← takeNat b)
  | .dealDamageToEachNonDragonThenAddDragonMana n =>
    return .dealDamageToEachNonDragonThenAddDragonMana (← takeNat n)
  | .millThenPutAllInstantsOrSorceries n => return .millThenPutAllInstantsOrSorceries (← takeNat n)
  | .exileTopPlayIfYouControlSubtype n s =>
    return .exileTopPlayIfYouControlSubtype (← takeNat n) (← takeStr s)
  | .lookAtTopLandsGainLife a b => return .lookAtTopLandsGainLife (← takeNat a) (← takeNat b)
  | .dealDamageTeamwork a b => return .dealDamageTeamwork (← takeNat a) (← takeNat b)
  | .dealDamageThenControllerIfTeamwork a b =>
    return .dealDamageThenControllerIfTeamwork (← takeNat a) (← takeNat b)
  | .counterUnlessPaysTeamwork a b => return .counterUnlessPaysTeamwork (← takeNat a) (← takeNat b)
  | .exileCreatureMvAtMostOrAnyIfTeamwork a b =>
    return .exileCreatureMvAtMostOrAnyIfTeamwork (← takeNat a) (← takeNat b)
  | .returnGyCreatureMvAtMostOrAny n => return .returnGyCreatureMvAtMostOrAny (← takeNat n)
  | .revealTopPutCreatures n => return .revealTopPutCreatures (← takeNat n)
  | .createTokens k n => return .createTokens k (← takeNat n)
  | .targetPlayerCreatesTokens k n => return .targetPlayerCreatesTokens k (← takeNat n)
  | .dealDamageToEachCreature n => return .dealDamageToEachCreature (← takeNat n)
  | .returnGySubtypeToHand s => return .returnGySubtypeToHand (← takeStr s)
  | .eachOpponentLosesLife n => return .eachOpponentLosesLife (← takeNat n)
  | .plusOneOnCreatureN n => return .plusOneOnCreatureN (← takeNat n)
  | .pumpThenDraw p t => return .pumpThenDraw (← takeInt p) (← takeInt t)
  | .pumpThenExileTopPlay p t => return .pumpThenExileTopPlay (← takeInt p) (← takeInt t)
  | .createTokensThenTeamPump k n p t =>
    return .createTokensThenTeamPump k (← takeNat n) (← takeInt p) (← takeInt t)
  | .createTokensPerSubtype k s => return .createTokensPerSubtype k (← takeStr s)
  | .creaturesYouControlGetAndGrant p t k =>
    return .creaturesYouControlGetAndGrant (← takeInt p) (← takeInt t) k
  | .millThenPutPermanentGainLife a b =>
    return .millThenPutPermanentGainLife (← takeNat a) (← takeNat b)
  | .gainLifeSearchBasicPlusOne n => return .gainLifeSearchBasicPlusOne (← takeNat n)
  | .copyThisSpellXTimesThenDamage n => return .copyThisSpellXTimesThenDamage (← takeNat n)
  | .mayPutHeroMvOrDraw n => return .mayPutHeroMvOrDraw (← takeNat n)
  | .maySacArtifactOrDiscardDraw n => return .maySacArtifactOrDiscardDraw (← takeNat n)
  | .artifactSpellsCostLessThisTurn n => return .artifactSpellsCostLessThisTurn (← takeNat n)
  | r => return r

def takeChapter (c : ChapterResolution) : ArgM ChapterResolution := do
  match c with
  | .dealDamageToOppCreature n => return .dealDamageToOppCreature (← takeNat n)
  | .elvesGetVigilance p => return .elvesGetVigilance (← takeInt p)
  | .amassGoblins n => return .amassGoblins (← takeNat n)
  | .opponentLosesYouGain n => return .opponentLosesYouGain (← takeNat n)
  | .draw n => return .draw (← takeNat n)
  | .searchBasicPlainsExileGainLife a b =>
    return .searchBasicPlainsExileGainLife (← takeNat a) (← takeNat b)
  | .returnCreatureFromGyMvAtMost n => return .returnCreatureFromGyMvAtMost (← takeNat n)
  | .gainControlOfUpToTwoCreaturesTotalMvAtMost n =>
    return .gainControlOfUpToTwoCreaturesTotalMvAtMost (← takeNat n)
  | .dealDamageToEachNonSubtypeAndOpponents n s =>
    return .dealDamageToEachNonSubtypeAndOpponents (← takeNat n) (← takeStr s)
  | .spell s =>
    return .spell { s with
      targeting := ← takeTargeting s.targeting
      resolution := ← takeSpell s.resolution }
  | c => return c

def takeEnter (e : EnterLeftover) : ArgM EnterLeftover := do
  match e with
  | .destroy k => return .destroy (← takeKind k)
  | .dealDamageUpToOne n => return .dealDamageUpToOne (← takeNat n)
  | e => return e

def takeWhen (w : SharedTriggerWhen) : ArgM SharedTriggerWhen := do
  match w with
  | .subtypeYouControlEnters s => return .subtypeYouControlEnters (← takeStr s)
  | .nthPlanCounter n => return .nthPlanCounter (← takeNat n)
  | .or a b => return .or (← takeWhen a) (← takeWhen b)
  | w => return w

mutual
def takeTrigger (e : SharedTrigger) : ArgM SharedTrigger := do
  match e with
  | .scry n => return .scry (← takeNat n)
  | .draw n => return .draw (← takeNat n)
  | .createTokens k n tapped => return .createTokens k (← takeNat n) tapped
  | .amassGoblins n => return .amassGoblins (← takeNat n)
  | .dividedDamage a b => return .dividedDamage (← takeNat a) (← takeNat b)
  | .plusOneOn k => return .plusOneOn (← takeKind k)
  | .sourceGets p t => return .sourceGets (← takeInt p) (← takeInt t)
  | .pumpTarget k p t => return .pumpTarget (← takeKind k) (← takeInt p) (← takeInt t)
  | .gainLife n => return .gainLife (← takeNat n)
  | .conniveTarget k => return .conniveTarget (← takeKind k)
  | .exileUntilLeaves k => return .exileUntilLeaves (← takeKind k)
  | .damageEachOpponent n => return .damageEachOpponent (← takeNat n)
  | .attachTo k => return .attachTo (← takeKind k)
  | .onPermanent k a => return .onPermanent (← takeKind k) (← takeAction a)
  | .onSource a => return .onSource (← takeAction a)
  | .mayDiscardDraw n => return .mayDiscardDraw (← takeNat n)
  | .targetOpponentDiscards n => return .targetOpponentDiscards (← takeNat n)
  | .millPlayer n => return .millPlayer (← takeNat n)
  | .amassOrcs n => return .amassOrcs (← takeNat n)
  | .pumpCause p t => return .pumpCause (← takeInt p) (← takeInt t)
  | .exileTarget k => return .exileTarget (← takeKind k)
  | .sourceGetsAndTeamTrample p => return .sourceGetsAndTeamTrample (← takeInt p)
  | .becomePT p t => return .becomePT (← takeInt p) (← takeInt t)
  | .pumpAndDamageOpponents n => return .pumpAndDamageOpponents (← takeNat n)
  | .plusOneAndLifelink k => return .plusOneAndLifelink (← takeKind k)
  | .drawThenDiscard n => return .drawThenDiscard (← takeNat n)
  | .mayDiscardHandDraw n => return .mayDiscardHandDraw (← takeNat n)
  | .damageBlockers n => return .damageBlockers (← takeNat n)
  | .grantFlying k => return .grantFlying (← takeKind k)
  | .amassThenAttach n => return .amassThenAttach (← takeNat n)
  | .gainLifeSearchBasicOnTop n => return .gainLifeSearchBasicOnTop (← takeNat n)
  | .targetOpponentLosesLife n => return .targetOpponentLosesLife (← takeNat n)
  | .plusOneVigilance n => return .plusOneVigilance (← takeNat n)
  | .exileOppGyCardOppsLoseLife n => return .exileOppGyCardOppsLoseLife (← takeNat n)
  | .creaturesYouControlPumpAndFirstStrike p =>
    return .creaturesYouControlPumpAndFirstStrike (← takeInt p)
  | .mayPayGenericDraw n => return .mayPayGenericDraw (← takeNat n)
  | .untapPlusOneIfSubtype s => return .untapPlusOneIfSubtype (← takeStr s)
  | .damageEqualSubtypeToEachOpponent s =>
    return .damageEqualSubtypeToEachOpponent (← takeStr s)
  | .dealDamageDestroyIfSubtype n s =>
    return .dealDamageDestroyIfSubtype (← takeNat n) (← takeStr s)
  | .lookAtTopRevealTypes n ts => return .lookAtTopRevealTypes (← takeNat n) (← takeStrs ts)
  | .putNonlandMvAtMostFromGy n => return .putNonlandMvAtMostFromGy (← takeNat n)
  | .othersGetAndOppsGet ss p t op ot =>
    return .othersGetAndOppsGet (← takeStrs ss) (← takeInt p) (← takeInt t)
      (← takeInt op) (← takeInt ot)
  | .millThenSubtypeToHand n s => return .millThenSubtypeToHand (← takeNat n) (← takeStr s)
  | .untapAttackersExtraCombat n => return .untapAttackersExtraCombat (← takeInt n)
  | .revealTopPutRandomCreature n => return .revealTopPutRandomCreature (← takeNat n)
  | .damageTargetOpponent n => return .damageTargetOpponent (← takeNat n)
  | .chapter n ce => return .chapter (← takeNat n) (← takeChapter ce)
  | .drawIfAttackedOrEnteredSubtype s => return .drawIfAttackedOrEnteredSubtype (← takeStr s)
  | .othersOfSubtypeGetEqualSourceToughness s =>
    return .othersOfSubtypeGetEqualSourceToughness (← takeStr s)
  | .scryAndPlan n => return .scryAndPlan (← takeNat n)
  | .drainAndPlan n => return .drainAndPlan (← takeNat n)
  | .planFinishCreateRobots n => return .planFinishCreateRobots (← takeNat n)
  | .planFinishDividedDamage n => return .planFinishDividedDamage (← takeNat n)
  | .surveil n => return .surveil (← takeNat n)
  | .onEnchanted a => return .onEnchanted (← takeAction a)
  | .attachThen a => return .attachThen (← takeAction a)
  | .enter e => return .enter (← takeEnter e)
  | e => return e

def takeResolution (r : Resolution) : ArgM Resolution := do
  match r with
  | .draw n => return .draw (← takeNat n)
  | .scry n => return .scry (← takeNat n)
  | .onPermanent a => return .onPermanent (← takeAction a)
  | .onSource a => return .onSource (← takeAction a)
  | .gainLife n => return .gainLife (← takeNat n)
  | .amassGoblins n => return .amassGoblins (← takeNat n)
  | .createTokens k n tapped => return .createTokens k (← takeNat n) tapped
  | .discard n => return .discard (← takeNat n)
  | .searchLandTypeToHand s => return .searchLandTypeToHand (← takeStr s)
  | .becomeSubtypeWithLandsPT s => return .becomeSubtypeWithLandsPT (← takeStr s)
  | .creaturesYouControlPump p t => return .creaturesYouControlPump (← takeInt p) (← takeInt t)
  | .mill n => return .mill (← takeNat n)
  | .subtypesGainMenace ss => return .subtypesGainMenace (← takeStrs ss)
  | .searchBasicBeholdSubtypeUntap s => return .searchBasicBeholdSubtypeUntap (← takeStr s)
  | .dealDamageToAny n => return .dealDamageToAny (← takeNat n)
  | .damageEachOpponent n => return .damageEachOpponent (← takeNat n)
  | .plusOneOnEachOtherSubtype s n =>
    return .plusOneOnEachOtherSubtype (← takeStr s) (← takeNat n)
  | .lookAtTopPutTypes n ts => return .lookAtTopPutTypes (← takeNat n) (← takeStrs ts)
  | .lookAtTopRevealArtifact n => return .lookAtTopRevealArtifact (← takeNat n)
  | .addAnyColorSpendOnlySubtype s => return .addAnyColorSpendOnlySubtype (← takeStr s)
  | .dealDamageToEachCreature n => return .dealDamageToEachCreature (← takeNat n)
  | .targetPlayerDraw n => return .targetPlayerDraw (← takeNat n)
  | .createTokensEqualSubtype k s => return .createTokensEqualSubtype k (← takeStr s)
  | .lookAtTopRevealSubtype n s => return .lookAtTopRevealSubtype (← takeNat n) (← takeStr s)
  | .millThenPutSubtypeOrEnchantment n s =>
    return .millThenPutSubtypeOrEnchantment (← takeNat n) (← takeStr s)
  | .returnGyCreatureThenPlusOne n => return .returnGyCreatureThenPlusOne (← takeNat n)
  | .becomeTypes ts p t k =>
    return .becomeTypes (← takeStrs ts) (← takeInt p) (← takeInt t) k
  | .targetSubtypeConnives s => return .targetSubtypeConnives (← takeStr s)
  | .sequence rs => return .sequence (← rs.mapM takeResolution)
  | .spell s => return .spell (← takeSpell s)
  | .trigger e => return .trigger (← takeTrigger e)
  | r => return r
end

def takeEffect (e : Effect) : ArgM Effect := do
  match e.resolution with
  | .trigger te =>
    return { e with resolution := .trigger (← takeTrigger te) }
  | _ =>
    let targeting ← takeTargeting e.targeting
    let resolution ← takeResolution e.resolution
    let maxTargets ← if e.maxTargets == 0 then pure e.maxTargets else takeNat e.maxTargets
    return { e with targeting, resolution, maxTargets }

def takeStatic (ab : StaticAbility) : ArgM StaticAbility := do
  match ab with
  | .otherCreaturesHaveTrample ss => return .otherCreaturesHaveTrample (← takeStrs ss)
  | .otherCreaturesGet ss p t =>
    return .otherCreaturesGet (← takeStrs ss) (← takeInt p) (← takeInt t)
  | .enchantedCreatureGets p t => return .enchantedCreatureGets (← takeInt p) (← takeInt t)
  | .equippedCreatureGets p t => return .equippedCreatureGets (← takeInt p) (← takeInt t)
  | .cantBlockUnlessYouControl ss => return .cantBlockUnlessYouControl (← takeStrs ss)
  | .cantBeBlockedExceptBy n => return .cantBeBlockedExceptBy (← takeNat n)
  | .enchantedIsOnlySubtypeCantAttackOrBlock s =>
    return .enchantedIsOnlySubtypeCantAttackOrBlock (← takeStr s)
  | .enchantedCreatureGetsAndHas p t k =>
    return .enchantedCreatureGetsAndHas (← takeInt p) (← takeInt t) k
  | .creaturesYouControlGet p t => return .creaturesYouControlGet (← takeInt p) (← takeInt t)
  | .hasteIfYouControlOtherSubtype s => return .hasteIfYouControlOtherSubtype (← takeStr s)
  | .cantAttackUnlessYouControlNOther n s =>
    return .cantAttackUnlessYouControlNOther (← takeNat n) (← takeStr s)
  | .legendaryCreaturesGetAndWard p t w =>
    return .legendaryCreaturesGetAndWard (← takeInt p) (← takeInt t) (← takeNat w)
  | .nonlegendaryCreaturesGet p t => return .nonlegendaryCreaturesGet (← takeInt p) (← takeInt t)
  | .equippedCreatureGetsAndHas p t k =>
    return .equippedCreatureGetsAndHas (← takeInt p) (← takeInt t) k
  | .equippedCreatureGetsAndWard p t w =>
    return .equippedCreatureGetsAndWard (← takeInt p) (← takeInt t) (← takeNat w)
  | .lifelinkIfYouControlOtherSubtype s => return .lifelinkIfYouControlOtherSubtype (← takeStr s)
  | .thresholdGets p t => return .thresholdGets (← takeInt p) (← takeInt t)
  | .cantBeBlockedByPowerAtMost n => return .cantBeBlockedByPowerAtMost (← takeInt n)
  | .getsAndHasIfEnduringStory p t k =>
    return .getsAndHasIfEnduringStory (← takeInt p) (← takeInt t) k
  | .creaturesYouControlGetIfEnduringStory p t =>
    return .creaturesYouControlGetIfEnduringStory (← takeInt p) (← takeInt t)
  | .artifactsAndCreaturesHaveWardIfEnduringStory n =>
    return .artifactsAndCreaturesHaveWardIfEnduringStory (← takeNat n)
  | .creaturesCantAttackYouUnlessPayIfEnduringStory n =>
    return .creaturesCantAttackYouUnlessPayIfEnduringStory (← takeNat n)
  | .otherSubtypeHaveTapAddOneOf ss m =>
    return .otherSubtypeHaveTapAddOneOf (← takeStrs ss) m
  | .cantBeBlockedByPowerAtLeast n => return .cantBeBlockedByPowerAtLeast (← takeInt n)
  | .equipAbilitiesTargetingThisCostLess n =>
    return .equipAbilitiesTargetingThisCostLess (← takeNat n)
  | .chosenTypeCreaturesGet p t => return .chosenTypeCreaturesGet (← takeInt p) (← takeInt t)
  | .otherSubtypeGetPowerPerArtifactToken s =>
    return .otherSubtypeGetPowerPerArtifactToken (← takeStr s)
  | .extraTriggerIfEnduringStorySubtype s =>
    return .extraTriggerIfEnduringStorySubtype (← takeStr s)
  | .extraTriggerAnotherYouControl ss b =>
    return .extraTriggerAnotherYouControl (← takeStrs ss) b
  | .powerPerFatGraveyard p => return .powerPerFatGraveyard (← takeInt p)
  | .copyActivatedFromGySubtype s => return .copyActivatedFromGySubtype (← takeStr s)
  | .equippedGetsTrampleAndCombatTreasures p t =>
    return .equippedGetsTrampleAndCombatTreasures (← takeInt p) (← takeInt t)
  | .creaturesYouControlOfSubtypeGet s p t =>
    return .creaturesYouControlOfSubtypeGet (← takeStr s) (← takeInt p) (← takeInt t)
  | .youAndOtherSubtypeHaveHexproofIfShield s =>
    return .youAndOtherSubtypeHaveHexproofIfShield (← takeStr s)
  | .subtypeSpellsCostLess s n => return .subtypeSpellsCostLess (← takeStr s) (← takeNat n)
  | .cantBeBlockedIfPowerAtMost n => return .cantBeBlockedIfPowerAtMost (← takeInt n)
  | .maximumHandSize n => return .maximumHandSize (← takeNat n)
  | .powerEqualSubtypeYouControl s => return .powerEqualSubtypeYouControl (← takeStr s)
  | .typeSpellsCostLess ty n => return .typeSpellsCostLess ty (← takeNat n)
  | .wardDiscardOrPay n => return .wardDiscardOrPay (← takeNat n)
  | .wardPoisonCounters n => return .wardPoisonCounters (← takeNat n)
  | .otherPowerUpCostsLess n => return .otherPowerUpCostsLess (← takeNat n)
  | .enchantedCreatureHasWard n => return .enchantedCreatureHasWard (← takeNat n)
  | .equippedCreatureGetsHasAndWard p t k w =>
    return .equippedCreatureGetsHasAndWard (← takeInt p) (← takeInt t) k (← takeNat w)
  | .opponentsCreaturesGet p t => return .opponentsCreaturesGet (← takeInt p) (← takeInt t)
  | .getsPowerPerOtherArtifact p => return .getsPowerPerOtherArtifact (← takeInt p)
  | .getsPowerPerAttachedEquipment p => return .getsPowerPerAttachedEquipment (← takeInt p)
  | .getsIfGyCreatureCards n p t =>
    return .getsIfGyCreatureCards (← takeNat n) (← takeInt p) (← takeInt t)
  | .enchantedCreatureGetsHasAndTypes p t k ts =>
    return .enchantedCreatureGetsHasAndTypes (← takeInt p) (← takeInt t) k (← takeStrs ts)
  | .enchantedCreatureGetsHasAndWard p t k w =>
    return .enchantedCreatureGetsHasAndWard (← takeInt p) (← takeInt t) k (← takeNat w)
  | .getsAndAllTypesIfGyCreatureCards n p t =>
    return .getsAndAllTypesIfGyCreatureCards (← takeNat n) (← takeInt p) (← takeInt t)
  | .sneak c => return .sneak (← takeCost c)
  | ab => return ab

def takeCostFields (c : ActivationCost) : ArgM ActivationCost := do
  let mana ← takeCost c.mana
  let payLife ← if c.payLife == 0 then pure c.payLife else takeNat c.payLife
  let sacrificeAnotherSubtype ← takeOptStr c.sacrificeAnotherSubtype
  return { c with mana, payLife, sacrificeAnotherSubtype }

def takeActivated (ab : ActivatedAbility) : ArgM ActivatedAbility := do
  let cost ← takeCostFields ab.cost
  let effect ← takeEffect ab.effect
  let otherModes ← ab.otherModes.mapM takeEffect
  let costReductionIfYouControlLegendary ←
    if ab.costReductionIfYouControlLegendary == 0 then pure 0
    else takeNat ab.costReductionIfYouControlLegendary
  let equipSubtype ← takeOptStr ab.equipSubtype
  let costReductionPerEquipment ←
    if ab.costReductionPerEquipment == 0 then pure 0 else takeNat ab.costReductionPerEquipment
  let onlyIfYouControlCreatureToughnessAtLeast ←
    if ab.onlyIfYouControlCreatureToughnessAtLeast == 0 then pure 0
    else takeNat ab.onlyIfYouControlCreatureToughnessAtLeast
  let onlyIfGyCreaturesAtLeast ←
    if ab.onlyIfGyCreaturesAtLeast == 0 then pure 0
    else takeNat ab.onlyIfGyCreaturesAtLeast
  let costReductionIfTargetPowerAtMost ←
    match ab.costReductionIfTargetPowerAtMost with
    | none => pure none
    | some (n, p) => pure (some (← takeNat n, ← takeInt p))
  return { ab with
    cost, effect, otherModes, costReductionIfYouControlLegendary, equipSubtype
    costReductionPerEquipment, onlyIfYouControlCreatureToughnessAtLeast
    onlyIfGyCreaturesAtLeast, costReductionIfTargetPowerAtMost }

def takeOpts (o : SharedTriggerOpts) : ArgM SharedTriggerOpts := do
  return { o with
    youControlCreatureWithPower := ← takeOptInt o.youControlCreatureWithPower
    thisOrNontokenSubtype := ← takeOptStr o.thisOrNontokenSubtype
    thisOrAnotherSubtype := ← takeOptStr o.thisOrAnotherSubtype
    anotherSubtypeOrEquipment := ← takeOptStr o.anotherSubtypeOrEquipment
    gainedLifeAtLeast := ← takeOptNat o.gainedLifeAtLeast
    anotherCreaturePowerAtMost := ← takeOptInt o.anotherCreaturePowerAtMost
    watchedSubtype := ← takeOptStr o.watchedSubtype }

def takeTriggered (ab : TriggeredAbility) : ArgM TriggeredAbility := do
  match ab with
  | .triggered w e o =>
    return .triggered (← takeWhen w) (← takeEffect e) (← takeOpts o)

def runCollect {α} (m : ArgM α) : Array SlotVal :=
  let (_, s) := m.run { mode := .collect, vals := [] }
  s.vals.reverse.toArray

def runFill {α} (m : ArgM α) (vals : Array SlotVal) : α :=
  (m.run { mode := .fill, vals := vals.toList }).1

def collectEffect (e : Effect) : Array SlotVal := runCollect (takeEffect e)
def collectStatic (ab : StaticAbility) : Array SlotVal := runCollect (takeStatic ab)
def collectActivated (ab : ActivatedAbility) : Array SlotVal := runCollect (takeActivated ab)
def collectTriggered (ab : TriggeredAbility) : Array SlotVal := runCollect (takeTriggered ab)

def singularize (s : String) : String :=
  match lowerAscii s with
  | "armies" => "Army"
  | "elves" => "Elf"
  | "wolves" => "Wolf"
  | "dwarves" => "Dwarf"
  | "heroes" => "Hero"
  | "merfolk" => "Merfolk"
  | low =>
    if low.endsWith "s" && low.length > 3 && !low.endsWith "ss" then
      capFirst (low.dropEnd 1).toString
    else capFirst low

def slotNat (vals : Array SlotVal) (i : Nat) : Nat :=
  match vals[i]? with
  | some (.nat n) => n
  | _ => 0

def slotInt (vals : Array SlotVal) (i : Nat) : Int :=
  match vals[i]? with
  | some (.int n) => n
  | some (.nat n) => n
  | _ => 0

def slotStr (vals : Array SlotVal) (i : Nat) : String :=
  match vals[i]? with
  | some (.str s) => s
  | _ => ""

def parseNatTok (t : String) : Option Nat :=
  if !t.isEmpty && t.all Char.isDigit then some t.toNat! else none

def parseIntTok (t : String) : Option Int :=
  if t.startsWith "+" || t.startsWith "-" then
    parseNatTok (t.drop 1).toString |>.map fun n => if t.startsWith "-" then -n else n
  else
    parseNatTok t |>.map fun n => (n : Int)

def renderNat (fmt : NatFmt) (n : Nat) : String :=
  match fmt with
  | .digits => toString n
  | .cards => cardPhrase n
  | .counters => plusOnePlusOneCountersPhrase n
  | .brace => s!"\{{n}}"
  | .english => englishNumber n

def renderInt (fmt : IntFmt) (i : Int) : String :=
  match fmt with
  | .signed => signedStat i
  | .digits => toString i

def renderStr (fmt : StrFmt) (s : String) : String :=
  match fmt with
  | .word _ => s
  | .plural => StaticAbility.pluralSubtype s
  | .cycling _ => s ++ "cycling"
  | .non => "non-" ++ s

def renderPt (signed : Bool) (p t : Int) : String :=
  if signed then s!"{signedStat p}/{signedStat t}" else s!"{p}/{t}"

structure Hit where
  width : Nat
  used : List Nat
  pat : Pat
  needle : String
  repl : String

def prefixTokens (pre toks : List String) : Bool :=
  pre.isPrefixOf toks

def consider (hits : List Hit) (h : Option Hit) : List Hit :=
  match h with
  | none => hits
  | some h => h :: hits

def bestHit (hits : List Hit) : Option Hit :=
  hits.foldl (fun best h =>
    match best with
    | none => some h
    | some b =>
      if h.width > b.width || (h.width == b.width && h.used.length < b.used.length) then
        some h
      else some b) none

def natHit (i : Nat) (fmt : NatFmt) (n : Nat) (toks : List String) (fresh : Bool) : Option Hit :=
  let needle := tokenize (lowerAscii (renderNat fmt n))
  if needle.isEmpty || !prefixTokens needle toks then none
  else some {
    width := needle.length
    used := if fresh then [i] else []
    pat := .nat i fmt
    needle := String.intercalate " " needle
    repl := renderNat fmt n
  }

def intHit (i : Nat) (fmt : IntFmt) (v : Int) (toks : List String) (fresh : Bool) : Option Hit :=
  let needle := tokenize (renderInt fmt v)
  if needle.isEmpty || !prefixTokens needle toks then none
  else some {
    width := needle.length
    used := if fresh then [i] else []
    pat := .int i fmt
    needle := String.intercalate " " needle
    repl := renderInt fmt v
  }

def strWords (s : String) : List String :=
  tokenize (lowerAscii s)

def strHit (i : Nat) (fmt : StrFmt) (s : String) (toks : List String) (fresh : Bool) : Option Hit :=
  let needle :=
    match fmt with
    | .word _ => strWords s
    | .plural => strWords (StaticAbility.pluralSubtype s)
    | .cycling _ =>
      let ws := strWords s
      match ws.dropLast with
      | [] => [lowerAscii s ++ "cycling"]
      | init => init ++ [ws.getLast! ++ "cycling"]
    | .non => ["non-" ++ lowerAscii s]
  if s.length < 2 || needle.isEmpty || !prefixTokens needle toks then none
  else some {
    width := needle.length
    used := if fresh then [i] else []
    pat := .str i fmt
    needle := String.intercalate " " needle
    repl := renderStr fmt s
  }

def ptHit (i j : Nat) (signed : Bool) (p t : Int) (toks : List String) (fresh : Bool) : Option Hit :=
  match toks with
  | tok :: _ =>
    let needle := renderPt signed p t
    if tok == needle then
      some {
        width := 1
        used := if fresh then [i, j] else []
        pat := .pt i j signed
        needle
        repl := needle
      }
    else none
  | [] => none

def hitsAt (args : Array SlotVal) (toks : List String) (used : List Nat) : List Hit :=
  Id.run do
    let mut hs : List Hit := []
    for i in [:args.size] do
      let fresh := !used.contains i
      match args[i]! with
      | .nat n =>
        for fmt in [NatFmt.cards, .counters, .brace, .english, .digits] do
          hs := consider hs (natHit i fmt n toks fresh)
      | .int v =>
        for fmt in [IntFmt.signed, .digits] do
          hs := consider hs (intHit i fmt v toks fresh)
        if fresh then
          for j in [:args.size] do
            if i < j && !used.contains j then
              match args[j]! with
              | .int t =>
                hs := consider hs (ptHit i j true v t toks true)
                hs := consider hs (ptHit i j false v t toks true)
              | _ => pure ()
      | .str s =>
        hs := consider hs (strHit i (.word (strWords s).length) s toks fresh)
        hs := consider hs (strHit i .plural s toks fresh)
        hs := consider hs (strHit i (.cycling (strWords s).length) s toks fresh)
        hs := consider hs (strHit i .non s toks fresh)
    return hs

/-- Prefer a still-unused argument, then the longest printed form. -/
def chooseHit (args : Array SlotVal) (toks : List String) (used : List Nat) : Option Hit :=
  let hs := hitsAt args toks used
  let fresh := hs.filter fun h => !h.used.isEmpty
  bestHit (if fresh.isEmpty then hs else fresh)

def patsOfTokens (args : Array SlotVal) (toks : List String) (used0 : List Nat := []) :
    List Pat × List Nat :=
  let rec go (fuel : Nat) (toks : List String) (used : List Nat) : List Pat × List Nat :=
    match fuel, toks with
    | 0, _ | _, [] => ([], used)
    | fuel + 1, tok :: _ =>
      match chooseHit args toks used with
      | some h =>
        let w := max h.width 1
        let (ps, used) := go fuel (toks.drop w) (h.used ++ used)
        (h.pat :: ps, used)
      | none =>
        let (ps, used) := go fuel (toks.drop 1) used
        (.lit tok :: ps, used)
  go toks.length toks used0

def patsOf (norm : String) (args : Array SlotVal) : List Pat :=
  (patsOfTokens args (tokenize norm)).1

/-- Patterns for several lines, so an argument spent on an earlier line is not
reused for a later one. -/
def patsOfLines (norms : List String) (args : Array SlotVal) : List (List Pat) :=
  let rec go (norms : List String) (used : List Nat) : List (List Pat) :=
    match norms with
    | [] => []
    | line :: rest =>
      let (pats, used) := patsOfTokens args (tokenize line) used
      pats :: go rest used
  go norms []

def setSlot (vals : Array SlotVal) (i : Nat) (v : SlotVal) (seen : List Nat) :
    Option (Array SlotVal × List Nat) :=
  if seen.contains i then
    if vals[i]? == some v then some (vals, seen) else none
  else if i < vals.size then some (vals.set! i v, i :: seen)
  else none

def matchPatsSeen (pats : List Pat) (toks : List String) (vals : Array SlotVal) (seen : List Nat) :
    Option (Array SlotVal × List Nat) :=
  let rec go (pats : List Pat) (toks : List String) (vals : Array SlotVal) (seen : List Nat) :
      Option (Array SlotVal × List Nat) :=
    match pats with
    | [] => if toks.isEmpty then some (vals, seen) else none
    | .lit s :: ps =>
      match toks with
      | t :: ts => if t == s then go ps ts vals seen else none
      | [] => none
    | .nat i fmt :: ps =>
      match fmt with
      | .cards =>
        match toks with
        | "a" :: "card" :: ts =>
          match setSlot vals i (.nat 1) seen with
          | some (vals, seen) => go ps ts vals seen
          | none => none
        | n :: "card" :: ts =>
          match parseNatTok n with
          | some k =>
            match setSlot vals i (.nat k) seen with
            | some (vals, seen) => go ps ts vals seen
            | none => none
          | none => none
        | n :: "cards" :: ts =>
          match parseNatTok n with
          | some k =>
            match setSlot vals i (.nat k) seen with
            | some (vals, seen) => go ps ts vals seen
            | none => none
          | none => none
        | _ => none
      | .counters =>
        match toks with
        | "a" :: "+1/+1" :: "counter" :: ts =>
          match setSlot vals i (.nat 1) seen with
          | some (vals, seen) => go ps ts vals seen
          | none => none
        | n :: "+1/+1" :: "counter" :: ts =>
          match parseNatTok n with
          | some k =>
            match setSlot vals i (.nat k) seen with
            | some (vals, seen) => go ps ts vals seen
            | none => none
          | none => none
        | n :: "+1/+1" :: "counters" :: ts =>
          match parseNatTok n with
          | some k =>
            match setSlot vals i (.nat k) seen with
            | some (vals, seen) => go ps ts vals seen
            | none => none
          | none => none
        | _ => none
      | .brace =>
        match toks with
        | t :: ts =>
          if t.startsWith "{" && t.endsWith "}" then
            match parseNatTok ((t.drop 1).dropEnd 1).toString with
            | some k =>
              match setSlot vals i (.nat k) seen with
              | some (vals, seen) => go ps ts vals seen
              | none => none
            | none => none
          else none
        | [] => none
      | .digits | .english =>
        match toks with
        | t :: ts =>
          match parseNatTok t with
          | some k =>
            match setSlot vals i (.nat k) seen with
            | some (vals, seen) => go ps ts vals seen
            | none => none
          | none => none
        | [] => none
    | .int i fmt :: ps =>
      match toks with
      | t :: ts =>
        match parseIntTok t with
        | some k =>
          let ok :=
            match fmt with
            | .signed => t.startsWith "+" || t.startsWith "-"
            | .digits => true
          if ok then
            match setSlot vals i (.int k) seen with
            | some (vals, seen) => go ps ts vals seen
            | none => none
          else none
        | none => none
      | [] => none
    | .str i fmt :: ps =>
      let take (n : Nat) (build : List String → String) : Option (Array SlotVal × List String × List Nat) :=
        let got := toks.take n
        if got.length != n then none
        else
          match setSlot vals i (.str (build got)) seen with
          | some (vals, seen) => some (vals, toks.drop n, seen)
          | none => none
      match fmt with
      | .word n =>
        match take n fun ws => capFirst (String.intercalate " " ws) with
        | some (vals, ts, seen) => go ps ts vals seen
        | none => none
      | .plural =>
        match toks with
        | t :: ts =>
          match setSlot vals i (.str (singularize t)) seen with
          | some (vals, seen) => go ps ts vals seen
          | none => none
        | [] => none
      | .cycling n =>
        match take n fun ws =>
          match ws.dropLast with
          | [] => capFirst ((ws.headD "").dropEnd "cycling".length).toString
          | init =>
            capFirst (String.intercalate " " (init ++
              [((ws.getLast!).dropEnd "cycling".length).toString]))
        with
        | some (vals, ts, seen) => go ps ts vals seen
        | none => none
      | .non =>
        match toks with
        | t :: ts =>
          if t.startsWith "non-" then
            match setSlot vals i (.str (capFirst (t.drop "non-".length).toString)) seen with
            | some (vals, seen) => go ps ts vals seen
            | none => none
          else none
        | [] => none
    | .pt i j signed :: ps =>
      match toks with
      | t :: ts =>
        match t.splitOn "/" with
        | [a, b] =>
          match parseIntTok a, parseIntTok b with
          | some p, some q =>
            let ok :=
              if signed then a.startsWith "+" || a.startsWith "-" else
                !a.startsWith "+"
            if ok then
              match setSlot vals i (.int p) seen with
              | none => none
              | some (vals, seen) =>
                match setSlot vals j (.int q) seen with
                | some (vals, seen) => go ps ts vals seen
                | none => none
            else none
          | _, _ => none
        | _ => none
      | [] => none
  go pats toks vals seen

def matchPats (pats : List Pat) (toks : List String) (vals : Array SlotVal) :
    Option (Array SlotVal) :=
  matchPatsSeen pats toks vals [] |>.map (·.1)

/-- First-line lookup keys. Digit runs are `#`, and `a card` / `N cards` share a key. -/
def lineKeys (s : String) : List String :=
  let rec skel (cs : List Char) (prevDigit : Bool) (acc : List Char) : List Char :=
    match cs with
    | [] => acc.reverse
    | c :: rest =>
      if c.isDigit then
        skel rest true (if prevDigit then acc else '#' :: acc)
      else skel rest false (c :: acc)
  let sk := String.ofList (skel s.toList false [])
  uniqueStrings [
    sk,
    sk.replace "# cards" "a card",
    sk.replace "a card" "# cards",
    sk.replace "# +1/+1 counters" "a +1/+1 counter",
    sk.replace "a +1/+1 counter" "# +1/+1 counters"
  ]

def patKey (pats : List (List Pat)) : String :=
  let piece : Pat → String
    | .lit s => s
    | .nat _ fmt =>
      match fmt with
      | .digits => "#d"
      | .cards => "#c"
      | .counters => "#k"
      | .brace => "#b"
      | .english => "#e"
    | .int _ fmt =>
      match fmt with
      | .signed => "#+"
      | .digits => "#i"
    | .str _ fmt =>
      match fmt with
      | .word n => s!"$w{n}"
      | .plural => "$p"
      | .cycling n => s!"$c{n}"
      | .non => "$n"
    | .pt _ _ signed => if signed then "+/+" else "#/#"
  String.intercalate "\n" (pats.map fun line => String.intercalate " " (line.map piece))

def renderHit (h : Hit) (vals : Array SlotVal) : String :=
  match h.pat with
  | .nat i fmt => renderNat fmt (slotNat vals i)
  | .int i fmt => renderInt fmt (slotInt vals i)
  | .str i fmt => renderStr fmt (slotStr vals i)
  | .pt i j signed => renderPt signed (slotInt vals i) (slotInt vals j)
  | .lit s => s

/-- Every way an argument can be spelled, independent of the surrounding line. -/
def allNeedles (args : Array SlotVal) : List Hit :=
  Id.run do
    let mut hs : List Hit := []
    for i in [:args.size] do
      match args[i]! with
      | .nat n =>
        for fmt in [NatFmt.cards, .counters, .brace, .english, .digits] do
          let needle := renderNat fmt n
          hs := { width := needle.length, used := [i], pat := .nat i fmt, needle, repl := needle } :: hs
      | .int v =>
        for fmt in [IntFmt.signed, .digits] do
          let needle := renderInt fmt v
          hs := { width := needle.length, used := [i], pat := .int i fmt, needle, repl := needle } :: hs
        for j in [:args.size] do
          if i < j then
            match args[j]! with
            | .int t =>
              for signed in [true, false] do
                let needle := renderPt signed v t
                hs := {
                  width := needle.length, used := [i, j], pat := .pt i j signed, needle, repl := needle
                } :: hs
            | _ => pure ()
      | .str s =>
        if s.length >= 2 then
          let word := .word (strWords s).length
          let cyc := .cycling (strWords s).length
          for fmt in [word, StrFmt.plural, cyc, StrFmt.non] do
            let needle := renderStr fmt s
            hs := { width := needle.length, used := [i], pat := .str i fmt, needle, repl := needle } :: hs
    return hs

def charHit (args : Array SlotVal) (cs : List Char) (prev : Option Char) (used : List Nat) :
    Option Hit :=
  let boundaryBefore :=
    match prev with
    | none => true
    | some p => !tokenChar p
  if !boundaryBefore || cs.isEmpty then none
  else
    let ok := (allNeedles args).filter fun h =>
      let n := h.needle.toList
      !n.isEmpty && n.isPrefixOf cs &&
        lowerAscii (String.ofList (cs.take n.length)) == lowerAscii h.needle &&
        match cs.drop n.length with
        | [] => true
        | c :: _ => !tokenChar c
    let fresh := ok.filter fun h => !h.used.isEmpty && h.used.all fun i => !used.contains i
    let pool :=
      if fresh.isEmpty then ok.filter fun h => h.used.all fun i => used.contains i else fresh
    bestHit pool

def splicePhrase (phrase : String) (old new : Array SlotVal) : String :=
  if phrase.isEmpty || old.size != new.size then phrase
  else
    let rec go (fuel : Nat) (cs : List Char) (prev : Option Char) (used : List Nat)
        (acc : List Char) : List Char :=
      match fuel, cs with
      | 0, _ | _, [] => acc.reverse
      | fuel + 1, c :: rest =>
        match charHit old cs prev used with
        | some h =>
          let repl := renderHit h new
          let replChars := repl.toList
          let n := max h.needle.length 1
          go fuel (cs.drop n) replChars.getLast? (h.used ++ used) (replChars.reverse ++ acc)
        | none => go fuel rest (some c) used (c :: acc)
    String.ofList (go phrase.length phrase.toList none [] [])

def finishEffect (old new : Effect) : Effect :=
  let oldArgs := collectEffect old
  let newArgs := collectEffect new
  match new.resolution with
  | .trigger (.chapter k (.spell s)) =>
    let s := { s with phrase := splicePhrase s.phrase oldArgs newArgs }
    let ce : ChapterResolution := .spell s
    let rebuilt := Effect.ofChapter ce
    { rebuilt with resolution := .trigger (.chapter k ce) }
  | .trigger (.chapter k ce) =>
    let rebuilt := Effect.ofChapter ce
    { rebuilt with resolution := .trigger (.chapter k ce) }
  | .trigger te =>
    let t := te.timing
    { new with
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      dividedDamage := t.dividedDamage
      phrase := "" }
  | _ => { new with phrase := splicePhrase old.phrase oldArgs newArgs }

def refillEffect (e : Effect) (vals : Array SlotVal) : Effect :=
  finishEffect e (runFill (takeEffect e) vals)

def refillStatic (ab : StaticAbility) (vals : Array SlotVal) : StaticAbility :=
  runFill (takeStatic ab) vals

def refillActivated (ab : ActivatedAbility) (vals : Array SlotVal) : ActivatedAbility :=
  let walked := runFill (takeActivated ab) vals
  let modes := (walked.otherModes.zip ab.otherModes).map fun (m, old) => finishEffect old m
  { walked with
    effect := finishEffect ab.effect walked.effect
    otherModes := modes }

def refillTriggered (ab : TriggeredAbility) (vals : Array SlotVal) : TriggeredAbility :=
  let walked := runFill (takeTriggered ab) vals
  match ab, walked with
  | .triggered _ e _, .triggered w e' o =>
    .triggered w (finishEffect e e') o

def setNat (e : Effect) (i n : Nat) : Effect :=
  refillEffect e ((collectEffect e).set! i (.nat n))

#guard refillEffect (Effect.draw 2) (collectEffect (Effect.draw 2)) == Effect.draw 2
#guard setNat (Effect.draw 2) 0 7 == Effect.draw 7
#guard setNat (Effect.draw 1) 0 4 == Effect.draw 4
#guard setNat (Effect.dealDamage 2) 0 5 == Effect.dealDamage 5
#guard setNat (Effect.scry 1) 0 3 == Effect.scry 3
#guard refillEffect (Effect.sourceGets 2 0) (collectEffect (Effect.sourceGets 2 0)) ==
  Effect.sourceGets 2 0

#guard
  let e := Effect.draw 2
  let args := collectEffect e
  match matchPats (patsOf (normalizeUnit "X" e.phrase) args)
      (tokenize (normalizeUnit "X" "draw 7 cards")) args with
  | some vals => refillEffect e vals == Effect.draw 7
  | none => false

#guard
  let e := Effect.searchLandTypeToHand "Mountain"
  let args := collectEffect e
  match matchPats (patsOf (normalizeUnit "X" e.phrase) args)
      (tokenize (normalizeUnit "X" (Effect.searchLandTypeToHand "Forest").phrase)) args with
  | some vals => refillEffect e vals == Effect.searchLandTypeToHand "Forest"
  | none => false

end Mtg.Engine.OracleArgs
