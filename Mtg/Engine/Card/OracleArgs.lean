import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.ChapterEffects
import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.OracleNorm
import Mtg.Engine.Card.TriggeredAbility

/-!
Argument values in modeled Oracle text.

A candidate ability is a shape. `Nat`, `Int`, `String`, and target-kind
arguments are read back out of the printed line, so a prototype such as
`Effect.draw 1` also matches “Draw seven cards,” and `Effect.destroyCreature`
also matches “Destroy target artifact.”
-/

namespace Mtg.Engine.OracleArgs

open OracleNorm

/-- One printed argument. A card type is any type from CR 205.2a. -/
inductive SlotVal where
  | nat (n : Nat)
  | int (i : Int)
  | str (s : String)
  | ty (t : CardType)
  | sup (s : Supertype)
  /-- The whole target noun (`target creature`, `target artifact token`, …). -/
  | kind (k : EffectTargetKind)
  /-- A counter kind (`+1/+1`, `stun`, `first strike`). -/
  | ctr (k : CounterKind)
  deriving BEq, Repr, Inhabited

inductive NatFmt where
  | digits
  | cards
  | counters
  | brace
  | english
  /-- `twice`, or `N times`. -/
  | times
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
  /-- Any CR 205.3 subtype, singular spelling, however many words it is. -/
  | sub
  /-- Any CR 205.3 subtype, plural spelling. -/
  | subPlural
  deriving BEq, Repr

/-- One token of a normalized Oracle line. A hole remembers which argument it is. -/
inductive Pat where
  | lit (s : String)
  | nat (i : Nat) (fmt : NatFmt)
  | int (i : Nat) (fmt : IntFmt)
  | str (i : Nat) (fmt : StrFmt)
  | ty (i : Nat)
  | sup (i : Nat)
  | kind (i : Nat)
  | pt (i j : Nat) (signed : Bool)
  /-- `a`/`an`/`N` plus a counter name plus `counter(s)`. `ni` is the count
  slot and `ki` is the `CounterKind` slot. -/
  | counterPhrase (ni ki : Nat)
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

def takeCardType (t : CardType) : ArgM CardType := do
  let s ← get
  match s.mode with
  | .collect =>
    set { s with vals := .ty t :: s.vals }
    return t
  | .fill =>
    match s.vals with
    | .ty v :: rest =>
      set { s with vals := rest }
      return v
    | _ => return t

def takeCounter (k : CounterKind) : ArgM CounterKind := do
  let s ← get
  match s.mode with
  | .collect =>
    set { s with vals := .ctr k :: s.vals }
    return k
  | .fill =>
    match s.vals with
    | .ctr v :: rest =>
      set { s with vals := rest }
      return v
    | _ => return k

def takeSupertype (sup : Supertype) : ArgM Supertype := do
  let s ← get
  match s.mode with
  | .collect =>
    set { s with vals := .sup sup :: s.vals }
    return sup
  | .fill =>
    match s.vals with
    | .sup v :: rest =>
      set { s with vals := rest }
      return v
    | _ => return sup

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

/-- One slot for the whole target kind, noun included.
Nested numbers stay inside the kind instead of becoming their own holes. -/
def takeWholeKind (k : EffectTargetKind) : ArgM EffectTargetKind := do
  let s ← get
  match s.mode with
  | .collect =>
    set { s with vals := .kind k :: s.vals }
    return k
  | .fill =>
    match s.vals with
    | .kind v :: rest =>
      set { s with vals := rest }
      return v
    | _ => return k

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
  | .anotherCreatureYouControlPowerAtMost n =>
    return .anotherCreatureYouControlPowerAtMost (← takeInt n)
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
  | .pumpAndExileIfDies p t => return .pumpAndExileIfDies (← takeInt p) (← takeInt t)
  | .setBasePT p t => return .setBasePT (← takeInt p) (← takeInt t)
  | a => return a

def takeSpell (r : SpellResolution) : ArgM SpellResolution := do
  match r with
  | .onPermanent a => return .onPermanent (← takeAction a)
  | .creaturesPump p t scope =>
    return .creaturesPump (← takeInt p) (← takeInt t) scope
  | .draw n who => return .draw (← takeNat n) who
  | .discard n => return .discard (← takeNat n)
  | .loseLife n who => return .loseLife (← takeNat n) who
  | .gainLife n who => return .gainLife (← takeNat n) who
  | .scry n => return .scry (← takeNat n)
  | .surveil n => return .surveil (← takeNat n)
  | .unlessPays r n => return .unlessPays (← takeSpell r) (← takeNat n)
  | .or rs => return .or (← rs.mapM takeSpell)
  | .may r => return .may (← takeSpell r)
  | .«if» r cond =>
    let r ← takeSpell r
    match cond with
    | .subtype s => return .«if» r (.subtype (← takeStr s))
    | .mvAtMost n => return .«if» r (.mvAtMost (← takeNat n))
    | .castFromGraveyard => return .«if» r .castFromGraveyard
  | .ifElse whenTrue whenFalse cond =>
    -- Printed order is the otherwise branch, then the condition, then the
    -- true branch.
    let whenFalse ← takeSpell whenFalse
    let cond ← match cond with
      | .subtype s => do
        let s ← takeStr s
        pure (.subtype s)
      | .mvAtMost n => do
        let n ← takeNat n
        pure (.mvAtMost n)
      | .castFromGraveyard => pure .castFromGraveyard
    let whenTrue ← takeSpell whenTrue
    return .ifElse whenTrue whenFalse cond
  | .countersOnCreatureTargets kind n which =>
    return .countersOnCreatureTargets (← takeCounter kind) (← takeNat n) which
  | .exileGraveyardCreaturesGrantCast ty =>
    return .exileGraveyardCreaturesGrantCast (← takeCardType ty)
  | .searchLegendaryCreatureToHand s ty =>
    return .searchLegendaryCreatureToHand (← takeSupertype s) (← takeCardType ty)
  | .addRedPerOppArtifacts ty => return .addRedPerOppArtifacts (← takeCardType ty)
  | .addFourManaDragonSpells n s =>
    return .addFourManaDragonSpells (← takeNat n) (← takeStr s)
  | .riddlesInTheDark n => return .riddlesInTheDark (← takeNat n)
  | .grantTrampleIfTeamwork kw => return .grantTrampleIfTeamwork (← takeStr kw)
  | .ownerMaySearchBasic s ty =>
    return .ownerMaySearchBasic (← takeSupertype s) (← takeCardType ty)
  | .onCreatureAmongTargets a => return .onCreatureAmongTargets (← takeAction a)
  | .becomeArtifactCreature44Flying p t kw =>
    return .becomeArtifactCreature44Flying (← takeInt p) (← takeInt t) (← takeStr kw)
  | .discardTwoUnlessArtifact n ty =>
    return .discardTwoUnlessArtifact (← takeNat n) (← takeCardType ty)
  | .plusOneOnEachYouControl n which =>
    return .plusOneOnEachYouControl (← takeNat n) which
  | .creatureYouControlDealsTwicePower k =>
    return .creatureYouControlDealsTwicePower (← takeNat k)
  | .mayDrawPerArtifactOppsDraw ty => return .mayDrawPerArtifactOppsDraw (← takeCardType ty)
  | .mayPutHeroMvOrDraw n s => return .mayPutHeroMvOrDraw (← takeNat n) (← takeStr s)
  | .amassGoblins n subtype =>
    return .amassGoblins (← takeNat n) (← takeStr subtype)
  | .dealDamageToEachCreature n which =>
    match which with
    | .each => return .dealDamageToEachCreature (← takeNat n)
    | .opponentsControl => return .dealDamageToEachCreature (← takeNat n) .opponentsControl
    | .nonSubtype subtype =>
      return .dealDamageToEachCreature (← takeNat n) (.nonSubtype (← takeStr subtype))
  | .millThenPut n which =>
    match which with
    | .oneOf a b =>
      return .millThenPut (← takeNat n) (.oneOf (← takeCardType a) (← takeCardType b))
    | .upTo max ty =>
      return .millThenPut (← takeNat n) (.upTo (← takeNat max) (← takeCardType ty))
    | .allOf a b =>
      return .millThenPut (← takeNat n) (.allOf (← takeCardType a) (← takeCardType b))
  | .exileTopPlayUntilNext n => return .exileTopPlayUntilNext (← takeNat n)
  | .exileTopPlayIfYouControlSubtype n s =>
    return .exileTopPlayIfYouControlSubtype (← takeNat n) (← takeStr s)
  | .lookAtTopLandsGainLife a b => return .lookAtTopLandsGainLife (← takeNat a) (← takeNat b)
  | .dealDamageTeamwork a b => return .dealDamageTeamwork (← takeNat a) (← takeNat b)
  | .damageControllerIfTeamwork n => return .damageControllerIfTeamwork (← takeNat n)
  | .counterUnlessPaysTeamwork a b => return .counterUnlessPaysTeamwork (← takeNat a) (← takeNat b)
  | .exileCreatureMvAtMostOrAnyIfTeamwork a b =>
    return .exileCreatureMvAtMostOrAnyIfTeamwork (← takeNat a) (← takeNat b)
  | .returnGyCreatureMvAtMostOrAny n => return .returnGyCreatureMvAtMostOrAny (← takeNat n)
  | .revealTopPutCreatures n => return .revealTopPutCreatures (← takeNat n)
  | .createTokens k n who => return .createTokens k (← takeNat n) who
  | .returnGySubtypeToHand s => return .returnGySubtypeToHand (← takeStr s)
  | .plusOneOnCreatureN n => return .plusOneOnCreatureN (← takeNat n)
  | .createTokensPerSubtype k s => return .createTokensPerSubtype k (← takeStr s)
  | .millThenPutPermanentGainLife a b =>
    return .millThenPutPermanentGainLife (← takeNat a) (← takeNat b)
  | .gainLifeSearchBasicPlusOne n => return .gainLifeSearchBasicPlusOne (← takeNat n)
  | .copyThisSpellXTimesThenDamage n => return .copyThisSpellXTimesThenDamage (← takeNat n)
  | .maySacArtifactOrDiscardDraw n => return .maySacArtifactOrDiscardDraw (← takeNat n)
  | .spellsCostLessThisTurn which n =>
    match which with
    | .cardType ty =>
      return .spellsCostLessThisTurn (.cardType (← takeCardType ty)) (← takeNat n)
    | .supertype s =>
      return .spellsCostLessThisTurn (.supertype (← takeSupertype s)) (← takeNat n)
  | .sequence rs => return .sequence (← rs.mapM takeSpell)
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
  | .destroy k => return .destroy (← takeWholeKind k)
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
  | .empowerJace n => return .empowerJace (← takeNat n)
  | .creaturesYouControlGet p t => return .creaturesYouControlGet (← takeInt p) (← takeInt t)
  | .mayPayPlusOneAndDraw n => return .mayPayPlusOneAndDraw (← takeNat n)
  | .plusOneOnEachSubtypeYouControl s => return .plusOneOnEachSubtypeYouControl (← takeStr s)
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
  | .becomeTypes ts p t k =>
    return .becomeTypes (← takeStrs ts) (← takeInt p) (← takeInt t) k
  | .targetSubtypeConnives s => return .targetSubtypeConnives (← takeStr s)
  | .empowerJace n => return .empowerJace (← takeNat n)
  | .exileTopMayCastElseDamageOpponents n => return .exileTopMayCastElseDamageOpponents (← takeNat n)
  | .emblemCastSpellDamage n => return .emblemCastSpellDamage (← takeNat n)
  | .surveil n => return .surveil (← takeNat n)
  | .millSelf n => return .millSelf (← takeNat n)
  | .mayDiscardDraw n => return .mayDiscardDraw (← takeNat n)
  | .targetPlayerLoseLife n => return .targetPlayerLoseLife (← takeNat n)
  | .controllerOfTargetLosesLife n => return .controllerOfTargetLosesLife (← takeNat n)
  | .fra (.loseLife n) => return .fra (.loseLife (← takeNat n))
  | .fra (.damageEachOpponent n) => return .fra (.damageEachOpponent (← takeNat n))
  | .fra (.damageAny n) => return .fra (.damageAny (← takeNat n))
  | .damageThenEmpowerExcess n => return .damageThenEmpowerExcess (← takeNat n)
  | .sequence rs => return .sequence (← rs.mapM takeResolution)
  | .spell s => return .spell (← takeSpell s)
  | .trigger e => return .trigger (← takeTrigger e)
  | r => return r
end

def takeEffect (e : Effect) : ArgM Effect := do
  match e.resolution with
  | .trigger te =>
    return { e with resolution := .trigger (← takeTrigger te) }
  | .onPermanent .destroy =>
    let kind ← takeWholeKind e.targeting.kind
    return { e with targeting := { e.targeting with kind } }
  | .onPermanent (.plusOne n) =>
    match e.targeting.kind with
    | .creatureYouControl | .creatureYouControlAnySubtype _ =>
      let kind ← takeWholeKind e.targeting.kind
      let n ← takeNat n
      return { e with
        targeting := { e.targeting with kind }
        resolution := .onPermanent (.plusOne n) }
    | _ => takeEffectRest e
  | _ => takeEffectRest e
where
  takeEffectRest (e : Effect) : ArgM Effect := do
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
  | .cantBeBlockedByMoreThan n => return .cantBeBlockedByMoreThan (← takeNat n)
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
  | .typeSpellsCostLess ty n =>
    return .typeSpellsCostLess (← takeCardType ty) (← takeNat n)
  | .supertypeSpellsCostLess s n =>
    return .supertypeSpellsCostLess (← takeSupertype s) (← takeNat n)
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
  match ofOracle? s with
  | some name => name
  | none =>
    let low := lowerAscii s
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

def slotTy (vals : Array SlotVal) (i : Nat) : CardType :=
  match vals[i]? with
  | some (.ty t) => t
  | _ => default

def slotSup (vals : Array SlotVal) (i : Nat) : Supertype :=
  match vals[i]? with
  | some (.sup s) => s
  | _ => default

def slotTarget (vals : Array SlotVal) (i : Nat) : EffectTargetKind :=
  match vals[i]? with
  | some (.kind k) => k
  | _ => .none

def slotCounter (vals : Array SlotVal) (i : Nat) : CounterKind :=
  match vals[i]? with
  | some (.ctr k) => k
  | _ => .plusOnePlusOne

/-- True when slot `i` is the count immediately after a counter kind.
`takeCounter` then `takeNat` lands in that order after `runCollect` reverses. -/
def isCounterCount (args : Array SlotVal) (i : Nat) : Bool :=
  i > 0 &&
    match args[i - 1]? with
    | some (.ctr _) => true
    | _ => false

def parseNatTok (t : String) : Option Nat :=
  if !t.isEmpty && t.all Char.isDigit then some t.toNat! else none

def parseIntTok (t : String) : Option Int :=
  if t.startsWith "+" || t.startsWith "-" then
    parseNatTok (t.drop 1).toString |>.map fun n => if t.startsWith "-" then -n else n
  else
    parseNatTok t |>.map fun n => (n : Int)

/-- Drop a literal token prefix. -/
def afterLits (toks lits : List String) : Option (List String) :=
  match lits with
  | [] => some toks
  | l :: ls =>
    match toks with
    | t :: ts => if t == l then afterLits ts ls else none
    | [] => none

/-- `prefix`, one integer, then `suffix`, as one target noun. -/
def withInt (toks : List String) (lead suffix : List String)
    (build : Int → Option EffectTargetKind) : Option (EffectTargetKind × Nat) :=
  match afterLits toks lead with
  | none => none
  | some rest =>
    match rest with
    | n :: after =>
      match parseIntTok n with
      | none => none
      | some i =>
        match build i, afterLits after suffix with
        | some k, some _ => some (k, lead.length + 1 + suffix.length)
        | _, _ => none
    | [] => none

def natKind (n : Int) (build : Nat → EffectTargetKind) : Option EffectTargetKind :=
  if n >= 0 then some (build n.toNat) else none

/-- `target Elf you control`, `target Goblin or Orc you control`, and
`target Bear, Spider, or Wolf you control` (commas already dropped). -/
def anySubtypeYouControl (toks : List String) : Option (EffectTargetKind × Nat) :=
  match afterLits toks ["target"] with
  | none => none
  | some rest =>
    let rec go (fuel : Nat) (acc : Array String) (ts : List String) (afterOr : Bool) :
        Option (Array String × List String) :=
      match fuel with
      | 0 => if acc.isEmpty || afterOr then none else some (acc, ts)
      | fuel + 1 =>
        match matchSubtypeForm false ts with
        | none => if acc.isEmpty || afterOr then none else some (acc, ts)
        | some (name, n) =>
          let rest := ts.drop n
          match rest with
          | "or" :: more =>
            if afterOr then none else go fuel (acc.push name) more true
          | _ =>
            if afterOr then some (acc.push name, rest)
            else
              match matchSubtypeForm false rest with
              | some _ => go fuel (acc.push name) rest false
              | none => some (acc.push name, rest)
    match go 4 #[] rest false with
    | some (ss, after) =>
      match afterLits after ["you", "control"] with
      | some left =>
        some (.creatureYouControlAnySubtype ss, toks.length - left.length)
      | none => none
    | none => none

/-- Longest target noun at the front of `toks` (already normalized). -/
def fromNounPrefix (toks : List String) : Option (EffectTargetKind × Nat) :=
  let closed := EffectTargetKind.closedKinds.filterMap fun k =>
    let n := tokenize (lowerAscii (EffectTargetKind.noun k))
    if n.isEmpty then none
    else if n.isPrefixOf toks then some (k, n.length) else none
  let numeric := [
    withInt toks ["target", "creature", "with", "power"] ["or", "greater"]
      fun n => some (.creaturePowerAtLeast n),
    withInt toks ["target", "creature", "with", "power"] ["or", "less"]
      fun n => some (.creaturePowerAtMost n),
    withInt toks ["target", "creature", "you", "control", "with", "power"] ["or", "less"]
      fun n => some (.creatureYouControlPowerAtMost n),
    withInt toks ["target", "creature", "an", "opponent", "controls", "with", "power"]
      ["or", "less"] fun n => some (.oppCreaturePowerAtMost n),
    withInt toks ["another", "target", "creature", "you", "control", "with", "power"]
      ["or", "less"] fun n => some (.anotherCreatureYouControlPowerAtMost n),
    withInt toks ["target", "creature", "with", "toughness"] ["or", "greater"]
      fun n => some (.creatureToughnessAtLeast n),
    withInt toks ["target", "creature", "with", "mana", "value"] ["or", "less"]
      fun n => natKind n .creatureMvAtMost,
    withInt toks ["target", "enchantment", "with", "mana", "value"] ["or", "greater"]
      fun n => natKind n .enchantmentMvAtLeast,
    withInt toks ["target", "creature", "spell", "with", "power", "or", "toughness"]
      ["or", "less"] fun n => natKind n .creatureSpellPTAtMost,
    withInt toks ["target", "creature", "card", "with", "mana", "value"]
      ["or", "less", "from", "your", "graveyard"]
      fun n => natKind n .creatureCardInYourGraveyardMvAtMost,
    withInt toks ["up", "to", "two", "target", "creatures", "with", "total", "mana", "value"]
      ["or", "less"] fun n => natKind n .upToTwoCreaturesTotalMvAtMost,
  ].filterMap id
  let subtype := anySubtypeYouControl toks
  (closed ++ numeric ++ subtype.toList).foldl (fun best c =>
    match best with
    | none => some c
    | some b => if c.2 > b.2 then some c else some b) none

def renderNat (fmt : NatFmt) (n : Nat) : String :=
  match fmt with
  | .digits => toString n
  | .cards => cardPhrase n
  | .counters => plusOnePlusOneCountersPhrase n
  | .brace => s!"\{{n}}"
  | .english => englishNumber n
  | .times => timesPhrase n

def renderInt (fmt : IntFmt) (i : Int) : String :=
  match fmt with
  | .signed => signedStat i
  | .digits => toString i

def renderStr (fmt : StrFmt) (s : String) : String :=
  match fmt with
  | .word _ | .sub => s
  | .plural | .subPlural => StaticAbility.pluralSubtype s
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
      -- The same text read as a counter phrase uses the count and the kind.
      -- Prefer that over the count alone. Different texts still prefer fewer slots.
      let better :=
        h.width > b.width ||
          (h.width == b.width && h.needle == b.needle && h.used.length > b.used.length) ||
          (h.width == b.width && h.needle != b.needle && h.used.length < b.used.length)
      if better then some h else some b) none

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

/-- A known subtype printed in this grammatical form. The hole later accepts
every CR 205.3 subtype, not only `s`. -/
def subHit (i : Nat) (fmt : StrFmt) (s : String) (toks : List String) (fresh : Bool) :
    Option Hit :=
  let found :=
    match fmt with
    | .sub => matchSubtypeForm false toks
    | .subPlural => matchSubtypeForm true toks
    | _ => none
  match found with
  | some (name, n) =>
    if subtypeKey name == subtypeKey s then
      some {
        width := n
        used := if fresh then [i] else []
        pat := .str i fmt
        needle := String.intercalate " " (toks.take n)
        repl := renderStr fmt s
      }
    else none
  | none => none

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
    | .non =>
      match strWords s with
      | [] => ["non-" ++ lowerAscii s]
      | w :: ws => ("non-" ++ w) :: ws
    | .sub | .subPlural => []
  if s.length < 2 || needle.isEmpty || !prefixTokens needle toks then none
  else some {
    width := needle.length
    used := if fresh then [i] else []
    pat := .str i fmt
    needle := String.intercalate " " needle
    repl := renderStr fmt s
  }

def tyHit (i : Nat) (t : CardType) (toks : List String) (fresh : Bool) : Option Hit :=
  let needle := tokenize (lowerAscii t.englishName)
  if needle.isEmpty || !prefixTokens needle toks then none
  else some {
    width := needle.length
    used := if fresh then [i] else []
    pat := .ty i
    needle := String.intercalate " " needle
    repl := t.englishName
  }

def kindHit (i : Nat) (k : EffectTargetKind) (toks : List String) (fresh : Bool) : Option Hit :=
  let needle := tokenize (lowerAscii (EffectTargetKind.noun k))
  if needle.isEmpty || !needle.isPrefixOf toks then none
  else some {
    width := needle.length
    used := if fresh then [i] else []
    pat := .kind i
    needle := String.intercalate " " needle
    repl := EffectTargetKind.noun k
  }

def supHit (i : Nat) (s : Supertype) (toks : List String) (fresh : Bool) : Option Hit :=
  let needle := tokenize (lowerAscii s.englishName)
  if needle.isEmpty || !prefixTokens needle toks then none
  else some {
    width := needle.length
    used := if fresh then [i] else []
    pat := .sup i
    needle := String.intercalate " " needle
    repl := s.englishName
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

def counterPhraseHit (ni ki : Nat) (n : Nat) (k : CounterKind) (toks : List String)
    (fresh : Bool) : Option Hit :=
  let needle := tokenize (lowerAscii (k.countersPhrase n))
  if needle.isEmpty || !prefixTokens needle toks then none
  else some {
    width := needle.length
    used := if fresh then [ni, ki] else []
    pat := .counterPhrase ni ki
    needle := String.intercalate " " needle
    repl := k.countersPhrase n
  }

def hitsAt (args : Array SlotVal) (toks : List String) (used : List Nat) : List Hit :=
  Id.run do
    let mut hs : List Hit := []
    for i in [:args.size] do
      let fresh := !used.contains i
      match args[i]! with
      | .nat n =>
        for fmt in [NatFmt.cards, .counters, .brace, .english, .digits, .times] do
          -- "up to one" normalizes to a bare `1`. Once the counter count is
          -- taken, that `1` stays a literal instead of a second use of the count.
          let skipReuse :=
            !fresh && isCounterCount args i && (fmt == .digits || fmt == .english)
          if !skipReuse then
            hs := consider hs (natHit i fmt n toks fresh)
        if isCounterCount args i then
          match args[i - 1]! with
          | .ctr k =>
            let kindFresh := fresh && !used.contains (i - 1)
            hs := consider hs (counterPhraseHit i (i - 1) n k toks kindFresh)
          | _ => pure ()
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
        if ofOracle? s |>.isSome then
          -- Plural first, then singular, so an invariant (`Merfolk`) learns
          -- the singular hole when both spellings are the same word.
          hs := consider hs (subHit i .subPlural s toks fresh)
          hs := consider hs (subHit i .sub s toks fresh)
          hs := consider hs (strHit i .non s toks fresh)
          hs := consider hs (strHit i (.cycling (strWords s).length) s toks fresh)
        else
          hs := consider hs (strHit i (.word (strWords s).length) s toks fresh)
          hs := consider hs (strHit i .plural s toks fresh)
          hs := consider hs (strHit i (.cycling (strWords s).length) s toks fresh)
          hs := consider hs (strHit i .non s toks fresh)
      | .ty t =>
        hs := consider hs (tyHit i t toks fresh)
      | .sup s =>
        hs := consider hs (supHit i s toks fresh)
      | .kind k =>
        hs := consider hs (kindHit i k toks fresh)
      | .ctr _ => pure ()
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
      | t :: ts =>
        let article (w : String) := w == "a" || w == "an"
        if t == s || (article t && article s) then go ps ts vals seen else none
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
      | .times =>
        match toks with
        | "twice" :: ts =>
          match setSlot vals i (.nat 2) seen with
          | some (vals, seen) => go ps ts vals seen
          | none => none
        | t :: "times" :: ts =>
          match parseNatTok t with
          | some k =>
            match setSlot vals i (.nat k) seen with
            | some (vals, seen) => go ps ts vals seen
            | none => none
          | none => none
        | _ => none
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
      let takeKnown (found : Option (String × Nat)) : Option (Array SlotVal × List Nat) :=
        match found with
        | some (name, n) =>
          match setSlot vals i (.str name) seen with
          | some (vals, seen) => go ps (toks.drop n) vals seen
          | none => none
        | none => none
      match fmt with
      | .sub => takeKnown (matchSubtypeForm false toks)
      | .subPlural => takeKnown (matchSubtypeForm true toks)
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
        match matchCyclingSubtype toks with
        | some (name, w) =>
          match setSlot vals i (.str name) seen with
          | some (vals, seen) => go ps (toks.drop w) vals seen
          | none => none
        | none =>
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
        match matchNonSubtype toks with
        | some (name, n) =>
          match setSlot vals i (.str name) seen with
          | some (vals, seen) => go ps (toks.drop n) vals seen
          | none => none
        | none =>
          match toks with
          | t :: ts =>
            if t.startsWith "non-" then
              match setSlot vals i (.str (capFirst (t.drop "non-".length).toString)) seen with
              | some (vals, seen) => go ps ts vals seen
              | none => none
            else none
          | [] => none
    | .ty i :: ps =>
      match toks with
      | t :: ts =>
        match CardType.ofOracle? t with
        | some ty =>
          match setSlot vals i (.ty ty) seen with
          | some (vals, seen) => go ps ts vals seen
          | none => none
        | none => none
      | [] => none
    | .sup i :: ps =>
      match toks with
      | t :: ts =>
        match Supertype.ofOracle? t with
        | some sup =>
          match setSlot vals i (.sup sup) seen with
          | some (vals, seen) => go ps ts vals seen
          | none => none
        | none => none
      | [] => none
    | .kind i :: ps =>
      match fromNounPrefix toks with
      | some (k, n) =>
        match setSlot vals i (.kind k) seen with
        | some (vals, seen) => go ps (toks.drop n) vals seen
        | none => none
      | none => none
    | .counterPhrase ni ki :: ps =>
      match CounterKind.matchPhrase toks with
      | some (n, k, w) =>
        match setSlot vals ni (.nat n) seen with
        | none => none
        | some (vals, seen) =>
          match setSlot vals ki (.ctr k) seen with
          | some (vals, seen) => go ps (toks.drop w) vals seen
          | none => none
      | none => none
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
      | .times => "#x"
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
      | .sub => "$s"
      | .subPlural => "$sp"
    | .ty _ => "$t"
    | .sup _ => "$sup"
    | .kind _ => "$k"
    | .pt _ _ signed => if signed then "+/+" else "#/#"
    | .counterPhrase _ _ => "#ctr"
  String.intercalate "\n" (pats.map fun line => String.intercalate " " (line.map piece))

def renderHit (h : Hit) (vals : Array SlotVal) : String :=
  match h.pat with
  | .nat i fmt => renderNat fmt (slotNat vals i)
  | .int i fmt => renderInt fmt (slotInt vals i)
  | .str i fmt => renderStr fmt (slotStr vals i)
  | .ty i => (slotTy vals i).englishName
  | .sup i => (slotSup vals i).englishName
  | .kind i => EffectTargetKind.noun (slotTarget vals i)
  | .pt i j signed => renderPt signed (slotInt vals i) (slotInt vals j)
  | .counterPhrase ni ki => (slotCounter vals ki).countersPhrase (slotNat vals ni)
  | .lit s => s

/-- Every way an argument can be spelled, independent of the surrounding line. -/
def allNeedles (args : Array SlotVal) : List Hit :=
  Id.run do
    let mut hs : List Hit := []
    for i in [:args.size] do
      match args[i]! with
      | .nat n =>
        for fmt in [NatFmt.cards, .counters, .brace, .english, .digits, .times] do
          -- A bare `1` is also "up to one". The counter phrase needle covers the count.
          let skipDigit :=
            isCounterCount args i && (fmt == .digits || fmt == .english)
          if !skipDigit then
            let needle := renderNat fmt n
            hs := { width := needle.length, used := [i], pat := .nat i fmt, needle, repl := needle } :: hs
        if isCounterCount args i then
          match args[i - 1]! with
          | .ctr k =>
            let needle := k.countersPhrase n
            hs := {
              width := needle.length, used := [i, i - 1], pat := .counterPhrase i (i - 1),
              needle, repl := needle
            } :: hs
          | _ => pure ()
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
          let fmts :=
            match ofOracle? s with
            | some _ =>
              [StrFmt.sub, .subPlural, .non, .cycling (strWords s).length]
            | none =>
              [.word (strWords s).length, StrFmt.plural,
                .cycling (strWords s).length, StrFmt.non]
          for fmt in fmts do
            let needle := renderStr fmt s
            hs := { width := needle.length, used := [i], pat := .str i fmt, needle, repl := needle } :: hs
      | .ty t =>
        let needle := lowerAscii t.englishName
        hs := { width := needle.length, used := [i], pat := .ty i, needle, repl := t.englishName } :: hs
      | .sup s =>
        let needle := lowerAscii s.englishName
        hs := { width := needle.length, used := [i], pat := .sup i, needle, repl := s.englishName } :: hs
      | .kind k =>
        let needle := lowerAscii (EffectTargetKind.noun k)
        if !needle.isEmpty then
          hs := {
            width := needle.length, used := [i], pat := .kind i, needle,
            repl := EffectTargetKind.noun k
          } :: hs
      | .ctr _ => pure ()
    return hs

/-- Replace each counter phrase (`a stun counter`, `2 shield counters`) with `$ctr`
so lines that differ only by kind and count share a lookup key. -/
def abstractCounterLine (s : String) : Option String :=
  let rec go (fuel : Nat) (ts : List String) : List String :=
    match fuel with
    | 0 => ts
    | fuel + 1 =>
      match CounterKind.matchPhrase ts with
      | some (_, _, w) =>
        let w := if w == 0 then 1 else w
        "$ctr" :: go fuel (ts.drop w)
      | none =>
        match ts with
        | [] => []
        | t :: rest => t :: go fuel rest
  let toks := tokenize s
  let out := String.intercalate " " (go toks.length toks)
  if out == String.intercalate " " toks then none else some out

#guard abstractCounterLine "put a +1/+1 counter on up to 1 target creature" ==
  some "put $ctr on up to 1 target creature"
#guard abstractCounterLine "put a stun counter on up to 1 target creature" ==
  some "put $ctr on up to 1 target creature"
#guard abstractCounterLine "put a first strike counter on it" ==
  some "put $ctr on it"
#guard abstractCounterLine "draw a card" == none

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
  | .onPermanent .destroy =>
    Effect.canonicalDestroy new.targeting.kind
  | .onPermanent (.plusOne n) =>
    match Effect.canonicalPlusOne n new.targeting.kind with
    | some e => e
    | none => { new with phrase := splicePhrase old.phrase oldArgs newArgs }
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
  let ab := StaticAbility.typeSpellsCostLess .artifact 1
  let args := collectStatic ab
  let query := StaticAbility.toNotation (.typeSpellsCostLess .sorcery 4)
  match matchPats (patsOf (normalizeUnit "X" (StaticAbility.toNotation ab)) args)
      (tokenize (normalizeUnit "X" query)) args with
  | some vals => refillStatic ab vals == .typeSpellsCostLess .sorcery 4
  | none => false

#guard
  let e := Effect.artifactSpellsCostLessThisTurn 1
  let args := collectEffect e
  let query := "Planeswalker spells you cast this turn cost {3} less to cast."
  match matchPats (patsOf (normalizeUnit "X" e.phrase) args)
      (tokenize (normalizeUnit "X" query)) args with
  | some vals =>
    (refillEffect e vals).resolution ==
      .spell (.spellsCostLessThisTurn (.cardType .planeswalker) 3)
  | none => false

/-- Refill `proto` from `query` and keep the resolution. -/
private def refilled (proto : Effect) (query : String) : Option Resolution :=
  let args := collectEffect proto
  match matchPats (patsOf (normalizeUnit "X" proto.phrase) args)
      (tokenize (normalizeUnit "X" query)) args with
  | some vals => some (refillEffect proto vals).resolution
  | none => none

#guard (Effect.amassGoblins 1).phrase == "amass Goblins 1"
#guard (Effect.riddlesInTheDark).phrase ==
  "look at the top four cards of your library and separate them into a face-down pile and a face-up pile. An opponent chooses one of the piles. Put that pile into your hand and the other into your graveyard"
#guard (Effect.plusOneOnEachYouControl).phrase ==
  "put a +1/+1 counter on each creature you control"
#guard (Effect.creatureYouControlDealsTwicePower).phrase ==
  "Target creature you control deals damage equal to twice its power to target creature an opponent controls."
#guard (Effect.drawThreeDiscardUnlessArtifact).phrase ==
  "draw three cards. Then discard two cards unless you discard an artifact card"

#guard refilled (Effect.amassGoblins 1) "amass Zombies 4" ==
  some (.spell (.amassGoblins 4 "Zombie"))

#guard refilled (Effect.riddlesInTheDark) "look at the top six cards of your library and separate them into a face-down pile and a face-up pile. An opponent chooses one of the piles. Put that pile into your hand and the other into your graveyard" ==
  some (.spell (.riddlesInTheDark 6))

#guard refilled (Effect.plusOneOnEachYouControl) "put 3 +1/+1 counters on each creature you control" ==
  some (.spell (.plusOneOnEachYouControl 3))

#guard Effect.plusOneThenEachOtherIfFromGy.phrase ==
  "put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control"

#guard refilled Effect.plusOneThenEachOtherIfFromGy
    "Put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control." ==
  some Effect.plusOneThenEachOtherIfFromGy.resolution

#guard refilled Effect.plusOneThenEachOtherIfFromGy
    "Put 2 +1/+1 counters on target creature you control. If this spell was cast from a graveyard, also put 3 +1/+1 counters on each other creature you control." ==
  some (.sequence [
    .spell (.countersOnCreatureTargets .plusOnePlusOne 2 .firstYouControl),
    .spell (.«if» (.plusOneOnEachYouControl 3 .eachOther) .castFromGraveyard)])

#guard (Effect.plusOneUpToOneAndPlayerGainsLife 2).phrase ==
  "put a +1/+1 counter on up to one target creature. Target player gains 2 life"

#guard refilled (Effect.plusOneUpToOneAndPlayerGainsLife 2)
    "Put a +1/+1 counter on up to one target creature. Target player gains 2 life." ==
  some (Effect.plusOneUpToOneAndPlayerGainsLife 2).resolution

#guard refilled (Effect.plusOneUpToOneAndPlayerGainsLife 2)
    "Put a stun counter on up to one target creature. Target player gains 4 life." ==
  some (Effect.plusOneUpToOneAndPlayerGainsLife 4 .stun).resolution

#guard refilled (Effect.plusOneUpToOneAndPlayerGainsLife 2)
    "Put two shield counters on up to one target creature. Target player gains 2 life." ==
  some (Effect.plusOneUpToOneAndPlayerGainsLife 2 .shield 2).resolution

#guard refilled (Effect.plusOneUpToOneAndPlayerGainsLife 2)
    "Put an indestructible counter on up to one target creature. Target player gains 2 life." ==
  some (Effect.plusOneUpToOneAndPlayerGainsLife 2 .indestructible).resolution

#guard refilled (Effect.plusOneUpToOneAndPlayerGainsLife 2)
    "Put a first strike counter on up to one target creature. Target player gains 1 life." ==
  some (Effect.plusOneUpToOneAndPlayerGainsLife 1 .firstStrike).resolution

#guard refilled (Effect.plusOneUpToOneAndPlayerGainsLife 2)
    "Put a -1/-1 counter on up to one target creature. Target player gains 2 life." ==
  some (Effect.plusOneUpToOneAndPlayerGainsLife 2 .minusOneMinusOne).resolution

#guard refilled (Effect.dealDamageToEachNonDragon 2) "deals 5 damage to each non-Elf creature" ==
  some (.spell (.dealDamageToEachCreature 5 (.nonSubtype "Elf")))

#guard refilled (Effect.searchLegendaryCreatureToHand)
    "search your library for a basic land card, reveal it, put it into your hand, then shuffle" ==
  some (.spell (.searchLegendaryCreatureToHand .basic .land))

#guard refilled (Effect.creatureYouControlDealsTwicePower)
    "Target creature you control deals damage equal to 3 times its power to target creature an opponent controls." ==
  some (.spell (.creatureYouControlDealsTwicePower 3))

#guard refilled (Effect.drawThreeDiscardUnlessArtifact)
    "draw three cards. Then discard four cards unless you discard an enchantment card" ==
  some (.sequence [.draw 3, .spell (.discardTwoUnlessArtifact 4 .enchantment)])

#guard refilled (Effect.becomeArtifactCreature44Flying)
    "until end of turn, target artifact or creature you control becomes an artifact creature with base power and toughness 2/3 and gains haste" ==
  some (.spell (.becomeArtifactCreature44Flying 2 3 "Haste"))

#guard refilled (Effect.mayDrawPerArtifactOppsDraw)
    "You may draw a card for each creature you control. If you do, each opponent draws a card" ==
  some (.spell (.mayDrawPerArtifactOppsDraw .creature))

#guard refilled (Effect.addRedPerOppArtifacts)
    "add {R} for each enchantment your opponents control" ==
  some (.spell (.addRedPerOppArtifacts .enchantment))

#guard CardType.all.all fun t =>
  let ab := StaticAbility.typeSpellsCostLess .artifact 1
  let args := collectStatic ab
  let query := StaticAbility.toNotation (.typeSpellsCostLess t 2)
  match matchPats (patsOf (normalizeUnit "X" (StaticAbility.toNotation ab)) args)
      (tokenize (normalizeUnit "X" query)) args with
  | some vals => refillStatic ab vals == .typeSpellsCostLess t 2
  | none => false

#guard Supertype.all.all fun s =>
  let ab := StaticAbility.supertypeSpellsCostLess .legendary 1
  let args := collectStatic ab
  let query := StaticAbility.toNotation (.supertypeSpellsCostLess s 2)
  match matchPats (patsOf (normalizeUnit "X" (StaticAbility.toNotation ab)) args)
      (tokenize (normalizeUnit "X" query)) args with
  | some vals => refillStatic ab vals == .supertypeSpellsCostLess s 2
  | none => false

#guard Supertype.all.all fun s =>
  let e := Effect.supertypeSpellsCostLessThisTurn 1
  let args := collectEffect e
  let query := s!"{s} spells you cast this turn cost \{{3}} less to cast."
  match matchPats (patsOf (normalizeUnit "X" e.phrase) args)
      (tokenize (normalizeUnit "X" query)) args with
  | some vals =>
    (refillEffect e vals).resolution ==
      .spell (.spellsCostLessThisTurn (.supertype s) 3)
  | none => false

#guard
  let e := Effect.draw 2
  let args := collectEffect e
  match matchPats (patsOf (normalizeUnit "X" e.phrase) args)
      (tokenize (normalizeUnit "X" "draw 7 cards")) args with
  | some vals => refillEffect e vals == Effect.draw 7
  | none => false

#guard
  let e := Effect.drawIfFromGy 1 2
  let args := collectEffect e
  match matchPats (patsOf (normalizeUnit "X" e.phrase) args)
      (tokenize (normalizeUnit "X"
        "Draw a card. If this spell was cast from a graveyard, draw two cards instead.")) args with
  | some vals => refillEffect e vals == Effect.drawIfFromGy 1 2
  | none => false

#guard
  let e := Effect.drawIfFromGy 1 2
  let args := collectEffect e
  match matchPats (patsOf (normalizeUnit "X" e.phrase) args)
      (tokenize (normalizeUnit "X"
        "Draw three cards. If this spell was cast from a graveyard, draw four cards instead.")) args with
  | some vals => refillEffect e vals == Effect.drawIfFromGy 3 4
  | none => false

#guard
  let e := Effect.amassGoblinsOrFromGy 1 3
  let args := collectEffect e
  match matchPats (patsOf (normalizeUnit "X" e.phrase) args)
      (tokenize (normalizeUnit "X"
        "Amass Goblins 1. If this spell was cast from a graveyard, amass Goblins 3 instead.")) args with
  | some vals => refillEffect e vals == Effect.amassGoblinsOrFromGy 1 3
  | none => false

#guard
  let e := Effect.amassGoblinsOrFromGy 1 3
  let args := collectEffect e
  match matchPats (patsOf (normalizeUnit "X" e.phrase) args)
      (tokenize (normalizeUnit "X"
        "Amass Zombies 2. If this spell was cast from a graveyard, amass Zombies 4 instead.")) args with
  | some vals =>
    (refillEffect e vals).resolution ==
      .spell (.ifElse (.amassGoblins 4 "Zombie") (.amassGoblins 2 "Zombie") .castFromGraveyard)
  | none => false

#guard
  let e := Effect.searchLandTypeToHand "Mountain"
  let args := collectEffect e
  match matchPats (patsOf (normalizeUnit "X" e.phrase) args)
      (tokenize (normalizeUnit "X" (Effect.searchLandTypeToHand "Forest").phrase)) args with
  | some vals => refillEffect e vals == Effect.searchLandTypeToHand "Forest"
  | none => false

/-- `Effect.destroyCreature` refills to `target` from the target noun alone. -/
private def matchesDestroy (target : Effect) : Bool :=
  let proto := Effect.destroyCreature
  let args := collectEffect proto
  match matchPats (patsOf (normalizeUnit "X" proto.phrase) args)
      (tokenize (normalizeUnit "X" target.phrase)) args with
  | some vals => refillEffect proto vals == target
  | none => false

#guard collectEffect Effect.destroyCreature == #[.kind .creature]
#guard matchesDestroy Effect.destroyCreature
#guard matchesDestroy Effect.destroyCreatureWithFlying
#guard matchesDestroy (Effect.destroyCreaturePowerAtLeast 4)
#guard matchesDestroy Effect.destroyTargetArtifact
#guard matchesDestroy Effect.destroyArtifactToken
#guard matchesDestroy Effect.destroyNoncreatureArtifact
#guard matchesDestroy Effect.destroyTargetColorlessNonland
#guard matchesDestroy Effect.destroyTargetPermanent
#guard matchesDestroy Effect.destroyTargetArtifactOrEnchantment
#guard matchesDestroy Effect.destroyTargetNoncreatureArtOrEnch
#guard
  let proto := Effect.destroyCreature
  let args := collectEffect proto
  let line := normalizeUnit "X" Effect.destroyArtifactOrLandNonflyersCantBlock.phrase
  matchPats (patsOf (normalizeUnit "X" proto.phrase) args) (tokenize line) args == none

/-- `Effect.plusOneOnTarget 2` refills to the other counter counts and subtype lists. -/
private def matchesPlus (target : Effect) : Bool :=
  let proto := Effect.plusOneOnTarget 2
  let args := collectEffect proto
  match matchPats (patsOf (normalizeUnit "X" proto.phrase) args)
      (tokenize (normalizeUnit "X" target.phrase)) args with
  | some vals => refillEffect proto vals == target
  | none => false

#guard matchesPlus (Effect.plusOneOnTarget 2)
#guard matchesPlus (Effect.plusOneOnTarget 1)
#guard matchesPlus (Effect.plusOneOnTarget 2 #["Elf"])
#guard matchesPlus (Effect.plusOneOnTarget 1 #["Goblin", "Orc"])
#guard matchesPlus (Effect.plusOneOnTarget 2 #["Bear", "Spider", "Wolf"])
#guard matchesPlus Effect.plusOneOnCreature
#guard
  let proto := Effect.plusOneOnTarget 2
  let args := collectEffect proto
  let line := normalizeUnit "X" "Put a +1/+1 counter on target creature. You gain 1 life"
  matchPats (patsOf (normalizeUnit "X" proto.phrase) args) (tokenize line) args == none

/-- One enters-and-destroy prototype refills to the other target noun. -/
private def matchesEnterDestroy (target : TriggeredAbility) : Bool :=
  let proto := TriggeredAbility.onEnter (Effect.enterDestroy .oppCreatureDealtDamageThisTurn)
  let args := collectTriggered proto
  let line := TriggeredAbility.toNotation proto
  match matchPats (patsOf (normalizeUnit "X" line) args)
      (tokenize (normalizeUnit "X" (TriggeredAbility.toNotation target))) args with
  | some vals => refillTriggered proto vals == target
  | none => false

#guard matchesEnterDestroy
  (TriggeredAbility.onEnter (Effect.enterDestroy .oppCreatureDealtDamageThisTurn))
#guard matchesEnterDestroy
  (TriggeredAbility.onEnter (Effect.enterDestroy (.oppCreaturePowerAtMost 3)))
#guard matchesEnterDestroy
  (TriggeredAbility.onEnter (Effect.enterDestroy .oppCreature))

#guard
  let noun := tokenize (lowerAscii (EffectTargetKind.noun .creatureYouControl))
  fromNounPrefix noun == some (.creatureYouControl, noun.length)
#guard
  let noun := tokenize (lowerAscii (EffectTargetKind.noun .legendaryCreatureYouControl))
  fromNounPrefix noun == some (.legendaryCreatureYouControl, noun.length)
#guard
  let noun := tokenize (lowerAscii (EffectTargetKind.noun .equipmentYouControl))
  fromNounPrefix noun == some (.equipmentYouControl, noun.length)

end Mtg.Engine.OracleArgs
