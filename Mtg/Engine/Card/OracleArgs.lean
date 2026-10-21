import Mtg.Engine.Card.ActivatedAbility
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
abbrev SlotVal := Nat ⊕ Int ⊕ String ⊕ CardType ⊕ Supertype ⊕ EffectTargetKind ⊕ CounterKind

namespace SlotVal

@[match_pattern] abbrev slotValKind (k : SlotVal := .inl 0) : SlotVal := k

@[match_pattern] abbrev nat (n : Nat) : SlotVal := slotValKind (.inl n)
@[match_pattern] abbrev int (i : Int) : SlotVal := slotValKind (.inr (.inl i))
@[match_pattern] abbrev str (s : String) : SlotVal := slotValKind (.inr (.inr (.inl s)))
@[match_pattern] abbrev ty (t : CardType) : SlotVal := slotValKind (.inr (.inr (.inr (.inl t))))
@[match_pattern] abbrev sup (s : Supertype) : SlotVal := slotValKind (.inr (.inr (.inr (.inr (.inl s)))))
/-- The whole target noun (`target creature`, `target artifact token`, …). -/
@[match_pattern] abbrev kind (k : EffectTargetKind) : SlotVal := slotValKind (.inr (.inr (.inr (.inr (.inr (.inl k))))))
/-- A counter kind (`+1/+1`, `stun`, `first strike`). -/
@[match_pattern] abbrev ctr (k : CounterKind) : SlotVal := slotValKind (.inr (.inr (.inr (.inr (.inr (.inr k))))))

end SlotVal

abbrev StrFmt := SpellCastKind

namespace _root_.Mtg.Engine.SpellCastKind

@[match_pattern] abbrev strFmtKind (n : Nat := 0) (k0 : Option Bool := Option.none) (b1 : Bool := false) (b2 : Bool := false) : SpellCastKind :=
  .spellCastKind (some n) Option.none Option.none b1 b2 false false false false k0

@[match_pattern] abbrev word (n : Nat) : StrFmt := strFmtKind n (some false) false false
@[match_pattern] abbrev cycling (n : Nat) : StrFmt := strFmtKind n (some false) true false
@[match_pattern] abbrev plural : StrFmt := strFmtKind 0 (some true) false false
@[match_pattern] abbrev non : StrFmt := strFmtKind 0 (some true) true false
/-- Any CR 205.3 subtype, singular spelling, however many words it is. -/
@[match_pattern] abbrev sub : StrFmt := strFmtKind 0 Option.none true false
/-- Any CR 205.3 subtype, plural spelling. -/
@[match_pattern] abbrev subPlural : StrFmt := strFmtKind 0 (some true) false true
@[match_pattern] abbrev natFmtKind (k0 : Option Bool := Option.none) (k1 : Bool := false) : StrFmt :=
  strFmtKind 0 k0 k1 true
@[match_pattern] abbrev intFmtKind (isDigits : Bool := false) : StrFmt :=
  strFmtKind 0 Option.none false isDigits
@[match_pattern] abbrev digits : StrFmt := strFmtKind 0 Option.none false true
@[match_pattern] abbrev cards : StrFmt := natFmtKind Option.none true
@[match_pattern] abbrev counters : StrFmt := natFmtKind (some false) false
@[match_pattern] abbrev brace : StrFmt := natFmtKind (some false) true
@[match_pattern] abbrev english : StrFmt := natFmtKind (some true) false
/-- `twice`, or `N times`. -/
@[match_pattern] abbrev times : StrFmt := natFmtKind (some true) true
@[match_pattern] abbrev signed : StrFmt := intFmtKind false
@[match_pattern] abbrev modeKind (isFill : Bool := false) : StrFmt := intFmtKind isFill
@[match_pattern] abbrev collect : StrFmt := modeKind false
@[match_pattern] abbrev fill : StrFmt := modeKind true

end _root_.Mtg.Engine.SpellCastKind

namespace StrFmt
export _root_.Mtg.Engine.SpellCastKind (
  strFmtKind word cycling plural non sub subPlural natFmtKind intFmtKind
  digits cards counters brace english times signed modeKind collect fill
)
end StrFmt

abbrev NatFmt := StrFmt

namespace NatFmt

@[match_pattern] abbrev natFmtKind (k0 : Option Bool := Option.none) (k1 : Bool := false) : NatFmt :=
  StrFmt.natFmtKind k0 k1
@[match_pattern] abbrev digits : NatFmt := StrFmt.digits
@[match_pattern] abbrev cards : NatFmt := StrFmt.cards
@[match_pattern] abbrev counters : NatFmt := StrFmt.counters
@[match_pattern] abbrev brace : NatFmt := StrFmt.brace
@[match_pattern] abbrev english : NatFmt := StrFmt.english
/-- `twice`, or `N times`. -/
@[match_pattern] abbrev times : NatFmt := StrFmt.times

end NatFmt

abbrev IntFmt := StrFmt

namespace IntFmt

@[match_pattern] abbrev intFmtKind (isDigits : Bool := false) : IntFmt := StrFmt.intFmtKind isDigits
@[match_pattern] abbrev signed : IntFmt := StrFmt.signed
@[match_pattern] abbrev digits : IntFmt := StrFmt.digits
@[match_pattern] abbrev modeKind (isFill : Bool := false) : IntFmt := StrFmt.modeKind isFill
@[match_pattern] abbrev collect : IntFmt := StrFmt.collect
@[match_pattern] abbrev fill : IntFmt := StrFmt.fill

end IntFmt

/-- One token of a normalized Oracle line. A hole remembers which argument it is. -/
abbrev Pat := TriggeredAbility.TargetObject

namespace _root_.Mtg.Engine.TargetObject

@[match_pattern] abbrev patKind (subtype : Option String := Option.none) (nOpt : Option Nat := Option.none)
    (boundOpt : Option Nat := Option.none) (fmtOpt : Option SpellCastKind := Option.none)
    (alt1 : Bool := false) (alt2 : Bool := false) (cat1 : Bool := false) : Pat :=
  .targetObjectKind Option.none Option.none Option.none subtype nOpt boundOpt fmtOpt Option.none Option.none Option.none alt1 alt2 false false cat1

@[match_pattern] abbrev lit (s : String) : Pat := patKind (some s)
@[match_pattern] abbrev nat (i : Nat) (fmt : NatFmt) : Pat := patKind Option.none (some i) Option.none (some fmt) false false false
@[match_pattern] abbrev int (i : Nat) (fmt : IntFmt) : Pat := patKind Option.none (some i) Option.none (some fmt) true false false
@[match_pattern] abbrev str (i : Nat) (fmt : StrFmt) : Pat := patKind Option.none (some i) Option.none (some fmt) false true false
@[match_pattern] abbrev ty (i : Nat) : Pat := patKind Option.none (some i) Option.none Option.none false false false
@[match_pattern] abbrev sup (i : Nat) : Pat := patKind Option.none (some i) Option.none Option.none true false false
@[match_pattern] abbrev kind (i : Nat) : Pat := patKind Option.none (some i) Option.none Option.none false true false
@[match_pattern] abbrev pt (i j : Nat) (signed : Bool) : Pat := patKind Option.none (some i) (some j) Option.none signed false true
/-- `a`/`an`/`N` plus a counter name plus `counter(s)`. `ni` is the count
slot and `ki` is the `CounterKind` slot. -/
@[match_pattern] abbrev counterPhrase (ni ki : Nat) : Pat := patKind Option.none (some ni) (some ki) Option.none false false false

end _root_.Mtg.Engine.TargetObject

namespace Pat
export _root_.Mtg.Engine.TargetObject (
  patKind lit nat int str ty sup kind pt counterPhrase
)
end Pat

abbrev Mode := IntFmt

namespace Mode

@[match_pattern] abbrev modeKind (isFill : Bool := false) : Mode := IntFmt.intFmtKind isFill
@[match_pattern] abbrev collect : Mode := modeKind false
@[match_pattern] abbrev fill : Mode := modeKind true

end Mode

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
    set { s with vals := SlotVal.nat n :: s.vals }
    return n
  | _ =>
    match s.vals with
    | SlotVal.nat v :: rest =>
      set { s with vals := rest }
      return v
    | _ => return n

def takeInt (i : Int) : ArgM Int := do
  let s ← get
  match s.mode with
  | .collect =>
    set { s with vals := SlotVal.int i :: s.vals }
    return i
  | _ =>
    match s.vals with
    | SlotVal.int v :: rest =>
      set { s with vals := rest }
      return v
    | _ => return i

def takeCardType (t : CardType) : ArgM CardType := do
  let s ← get
  match s.mode with
  | .collect =>
    set { s with vals := SlotVal.ty t :: s.vals }
    return t
  | _ =>
    match s.vals with
    | SlotVal.ty v :: rest =>
      set { s with vals := rest }
      return v
    | _ => return t

def takeCounter (k : CounterKind) : ArgM CounterKind := do
  let s ← get
  match s.mode with
  | .collect =>
    set { s with vals := SlotVal.ctr k :: s.vals }
    return k
  | _ =>
    match s.vals with
    | SlotVal.ctr v :: rest =>
      set { s with vals := rest }
      return v
    | _ => return k

def takeSupertype (sup : Supertype) : ArgM Supertype := do
  let s ← get
  match s.mode with
  | .collect =>
    set { s with vals := SlotVal.sup sup :: s.vals }
    return sup
  | _ =>
    match s.vals with
    | SlotVal.sup v :: rest =>
      set { s with vals := rest }
      return v
    | _ => return sup

def takeStr (str : String) : ArgM String := do
  let s ← get
  match s.mode with
  | .collect =>
    set { s with vals := SlotVal.str str :: s.vals }
    return str
  | _ =>
    match s.vals with
    | SlotVal.str v :: rest =>
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
    set { s with vals := SlotVal.kind k :: s.vals }
    return k
  | _ =>
    match s.vals with
    | SlotVal.kind v :: rest =>
      set { s with vals := rest }
      return v
    | _ => return k

def takeKind (k : @& EffectTargetKind) : ArgM EffectTargetKind := do
  match k with
  | .creatureYouControlSubtype s => return .creatureYouControlSubtype (← takeStr s)
  | .creatureSpellPTAtMost n => return .creatureSpellPTAtMost (← takeNat n)
  | .battlefield (.creatureStatAtLeast n toughness) =>
    return .battlefield (.creatureStatAtLeast (← takeInt n) toughness)
  | .battlefield (.creaturePowerAtMost n controller another) =>
    return .battlefield (.creaturePowerAtMost (← takeInt n) controller another)
  | .creatureYouControlAnySubtype ss => return .creatureYouControlAnySubtype (← takeStrs ss)
  | .creatureCardInYourGraveyardMvAtMost n =>
    return .creatureCardInYourGraveyardMvAtMost (← takeNat n)
  | .creatureMvAtMost n => return .creatureMvAtMost (← takeNat n)
  | .enchantmentMvAtLeast n => return .enchantmentMvAtLeast (← takeNat n)
  | .upToTwoCreaturesTotalMvAtMost n => return .upToTwoCreaturesTotalMvAtMost (← takeNat n)
  | k => return k

def takeTargeting (t : @& EffectTargeting) : ArgM EffectTargeting := do
  return { t with kind := ← takeKind t.kind }

def takeWhen (w : @& SharedTriggerWhen) : ArgM SharedTriggerWhen := do
  match w with
  | .subtypeYouControlEnters s => return .subtypeYouControlEnters (← takeStr s)
  | .youAttackWithTotalPower n => return .youAttackWithTotalPower (← takeInt n)
  | .nthPlanCounter n => return .nthPlanCounter (← takeNat n)
  | .sagaChapter n => return .sagaChapter (← takeNat n)
  | .or a b => return .or (← takeWhen a) (← takeWhen b)
  | w => return w

def takeResolutionCombat (r : @& Resolution) : ArgM Resolution := do
  match r with
  | .pump power toughness who =>
    match power, toughness, who with
    | .fixed p, .fixed t, _ =>
      return .pump (.fixed (← takeInt p)) (.fixed (← takeInt t)) who
    | .equalSourceToughness, .equalSourceToughness, .othersOfSubtype s =>
      return .pump .equalSourceToughness .equalSourceToughness (.othersOfSubtype (← takeStr s))
    | _, _, _ => return r
  | .dealDamage amount who note =>
    match amount, who, note with
    | .fixed 0, .target, .preallocated =>
      return .dealDamage (.fixed 0) .target .preallocated
    | .subtypeCount s, .player .eachOpponent, _ =>
      return .dealDamage (.subtypeCount (← takeStr s)) (.player .eachOpponent) note
    | .fixed n, .nonSubtypeCreatures subtype, _ =>
      return .dealDamage (.fixed (← takeNat n.toNat)) (.nonSubtypeCreatures (← takeStr subtype)) note
    | .fixed n, .eachNonSubtypeAndOpponents subtype, _ =>
      return .dealDamage (.fixed (← takeNat n.toNat)) (.eachNonSubtypeAndOpponents (← takeStr subtype)) note
    | .fixed n, _, _ =>
      return .dealDamage (.fixed (← takeNat n.toNat)) who note
    | _, _, _ => return r
  | r => return r

def takeResolutionGrant (r : @& Resolution) (what : @& TriggeredAbility.TriggerGrantWhat) (who : @& ObjectSelector) : ArgM Resolution := do
  match what, who with
  | .subtypeWithLandsPT s, .source =>
    return .grant (.subtypeWithLandsPT (← takeStr s)) .source
  | .keywords k, .intersection [.creaturesYouControl, .union whatList] =>
    let ss := (whatList.filterMap fun | .youControl (.subtype s) => some s | _ => none).toArray
    let ss ← takeStrs ss
    return .grant (.keywords k)
      (.intersection [.creaturesYouControl, .union (ss.toList.map (fun s => .youControl (.subtype s)))])
  | .typesPTAndKeywords ts p t k, .source =>
    return .grant (.typesPTAndKeywords (← takeStrs ts) (← takeInt p) (← takeInt t) k) .source
  | .connive, .target (.youControl (.subtype s)) =>
    return .connive (.target (.youControl (.subtype (← takeStr s))))
  | .empowerJace (.fixed n), .youIfCast =>
    return .empowerJace (← takeNat n.toNat)
  | .emblemCastSpellDamage n, .youIfCast =>
    return .grant (.emblemCastSpellDamage (← takeNat n)) .youIfCast
  | .basePT (.fixed p) (.fixed t), _ =>
    return .setBasePT (.fixed (← takeInt p)) (.fixed (← takeInt t)) who
  | .artifactCreature p t kw, .target =>
    return .grant (.artifactCreature (← takeInt p) (← takeInt t) (← takeStr kw)) .target
  | .fight (.timesPower k), .announced =>
    if k == 1 then return .fight .announced (.timesPower 1)
    else return .fight .announced (.timesPower (← takeNat k))
  | .spellsCostLess which (.fixed n), .youIfCast =>
    match which with
    | .supertype s =>
      return .spellsCostLess (.supertype (← takeSupertype s)) (.fixed (← takeNat n.toNat))
    | .milledPickKind ty _ _ _ _ =>
      return .spellsCostLess (.cardType (← takeCardType ty)) (.fixed (← takeNat n.toNat))
    | _ => return r
  | _, _ => return r

def takeResolutionPlayerResource (r : @& Resolution) : ArgM Resolution := do
  match r with
  | .mill amount who note =>
    match amount, note with
    | .fixed n, .subtypeOrEnchantmentToHand s =>
      return .mill (.fixed (← takeNat n.toNat)) who (.subtypeOrEnchantmentToHand (← takeStr s))
    | .fixed n, .none => return .mill (← takeNat n.toNat) who .none
    | .fixed n, .milledCards => return .mill (← takeNat n.toNat) who .milledCards
    | .fixed n, .toHand which =>
      match which with
      | .oneOf a b =>
        return .mill (.fixed (← takeNat n.toNat)) who (.toHand (.oneOf (← takeCardType a) (← takeCardType b)))
      | .upTo max ty =>
        return .mill (.fixed (← takeNat n.toNat)) who (.toHand (.upTo (← takeNat max) (← takeCardType ty)))
      | .milledPickKind a b _ _ _ =>
        return .mill (.fixed (← takeNat n.toNat)) who (.toHand (.allOf (← takeCardType a) (← takeCardType b)))
      | _ => return r
    | .fixed a, .permanentAndGainLife b =>
      return .mill (.fixed (← takeNat a.toNat)) who (.permanentAndGainLife (← takeNat b))
    | _, _ => return r
  | .addMana types amount note =>
    match amount, note with
    | _, .subtypeSpellsOrAbilities s =>
      return .addMana types amount (.subtypeSpellsOrAbilities (← takeStr s))
    | .count (.oppPermanents ty), _ =>
      return .addMana types (.count (.oppPermanents (← takeCardType ty))) note
    | .fixed n, .subtypeSpells s =>
      return .addMana types (.fixed (← takeNat n.toNat)) (.subtypeSpells (← takeStr s))
    | _, _ => return r
  | .draw (.fixed n) who => return .draw (← takeNat n.toNat) who
  | .loseLife (.fixed n) who => return .loseLife (← takeNat n.toNat) who
  | .gainLife (.fixed n) who => return .gainLife (← takeNat n.toNat) who
  | .scry (.fixed n) => return .scry (← takeNat n.toNat)
  | .surveil (.fixed n) note => return .surveil (← takeNat n.toNat) note
  | r => return r

def takeResolutionTapDiscardOrReturn (r : @& Resolution) : ArgM Resolution := do
  match r with
  | .discard what =>
    match what with
    | .cards n => return .discard (.cards (← takeNat n))
    | .cards n (.target .opponent) =>
      return .discard (.cards (← takeNat n) (.target .opponent))
    | .cardsUnlessType n ty =>
      return .discard (.cardsUnlessType (← takeNat n) (← takeCardType ty))
    | _ => return r
  | .returnToHand what note =>
    match what with
    | .graveyardSubtype s =>
      return .returnToHand (.graveyardSubtype (← takeStr s)) note
    | .milledSubtype s =>
      return .returnToHand (.milledSubtype (← takeStr s)) note
    | _ => return r
  | r => return r

def takeResolutionTokensOrCounters (r : @& Resolution) : ArgM Resolution := do
  match r with
  | .putCounters what who =>
    match what, who with
    | .ofKind kind n, .creatureTargets =>
      return .putCounters (.ofKind (← takeCounter kind) (← takeNat n)) .creatureTargets
    | .ofKind kind n, .firstTargetCreatureYouControl =>
      return .putCounters (.ofKind (← takeCounter kind) (← takeNat n)) .firstTargetCreatureYouControl
    | .ofKind .plusOnePlusOne 1, .youControl (.subtype s) =>
      return .putCounters (.ofKind .plusOnePlusOne 1) (.youControl (.subtype (← takeStr s)))
    | .ofKind .plusOnePlusOne n, .youControl =>
      return .putCounters (.ofKind .plusOnePlusOne (← takeNat n)) .youControl
    | .ofKind .plusOnePlusOne n, .eachOther =>
      return .putCounters (.ofKind .plusOnePlusOne (← takeNat n)) .eachOther
    | .ofKind .plusOnePlusOne n, .permanent =>
      return .putCounters (.ofKind .plusOnePlusOne (← takeNat n)) .permanent
    | .ofKind .plusOnePlusOne n, .source =>
      return .putCounters (.ofKind .plusOnePlusOne (← takeNat n)) .source
    | .ofKind .plusOnePlusOne n, .enchanted =>
      return .putCounters (.ofKind .plusOnePlusOne (← takeNat n)) .enchanted
    | .ofKind .plusOnePlusOne n, (.target .whileSource) =>
      return .putCounters (.ofKind .plusOnePlusOne (← takeNat n)) (.target .whileSource)
    | .ofKind .plusOnePlusOne n, .othersOfSubtype s =>
      let s ← takeStr s
      let n ← takeNat n
      return .putCounters (.ofKind .plusOnePlusOne n) (.othersOfSubtype s)
    | _, _ => return r
  | .amass amount subtype attach who =>
    match amount, who with
    | .fixed n, .you =>
      return .amass (.fixed (← takeNat n.toNat)) (← takeStr subtype) attach .you
    | .lastKnownPower, .you =>
      return .amass .lastKnownPower (← takeStr subtype) attach .you
    | _, _ => return r
  | .createTokens k amount tapped who note =>
    match amount with
    | .fixed n =>
      return .createTokens k (← takeNat n.toNat) tapped who note
    | .chosenX =>
      return .createTokens k .chosenX tapped who note
    | .perSubtype s =>
      return .createTokens k (.perSubtype (← takeStr s)) tapped who note
    | _ => return r
  | r => return r

def takeResolutionPutExileOrDestroy (r : @& Resolution) : ArgM Resolution := do
  match r with
  | .exile what how note =>
    match what, how, note with
    | .top, .mayCastElseDamageOpponents n, _ =>
      return .exile .top (.mayCastElseDamageOpponents (← takeNat n)) note
    | .graveyardCardsOfType ty (.target .player), .anyManaWhileExiled, _ =>
      return .exile (.graveyardCardsOfType (← takeCardType ty) (.target .player)) .anyManaWhileExiled note
    | .topN n, .playUntilNextTurn, _ =>
      return .exile (.topN (← takeNat n)) .playUntilNextTurn note
    | .topN n, .playIfYouControlSubtype s, _ =>
      return .exile (.topN (← takeNat n)) (.playIfYouControlSubtype (← takeStr s)) note
    | .creatureMvAtMostOrTeamwork a, .forLater, .gainLifeIfTeamwork b =>
      return .exile (.creatureMvAtMostOrTeamwork (← takeNat a)) .forLater (.gainLifeIfTeamwork (← takeNat b))
    | _, _, _ => return r
  | .put (.creatureMvAtMostOrTeamwork n) .asPrinted pnote =>
    return .put (.creatureMvAtMostOrTeamwork (← takeNat n)) .asPrinted pnote
  | r => return r

def takeResolutionRevealLibrary (r : @& Resolution) : ArgM Resolution := do
  match r with
  | .searchLibrary thenDo =>
    match thenDo with
    | .returnToHand (.landSubtype s) note =>
      return .searchLibrary (.returnToHand (.landSubtype (← takeStr s)) note)
    | .put (.basicBeholdUntap s) how note =>
      return .searchLibrary (.put (.basicBeholdUntap (← takeStr s)) how note)
    | .returnToHand (.supertypeCard s ty) note =>
      return .searchLibrary (.returnToHand (.supertypeCard (← takeSupertype s) (← takeCardType ty)) note)
    | .put (.supertypeCard s ty) how note =>
      return .searchLibrary (.put (.supertypeCard (← takeSupertype s) (← takeCardType ty)) how note)
    | .exile (.basicUpTo s max) .forLater .linked =>
      return .searchLibrary (.exile (.basicUpTo s (← takeNat max)) .forLater .linked)
    | _ => return r
  | .revealLibrary how thenDo rwho =>
    match how, thenDo with
    | .topNumber (.fixed n), .returnToHand (.lookedTypes ts) hnote =>
      return .revealLibrary (.topNumber (.fixed (← takeNat n.toNat))) (.returnToHand (.lookedTypes (← takeStrs ts)) hnote) rwho
    | .top n, .put (.lookedTypes ts) howPut pnote =>
      return .revealLibrary (.top (← takeNat n)) (.put (.lookedTypes (← takeStrs ts)) howPut pnote) rwho
    | .top n, .put .randomCreature howPut pnote =>
      return .revealLibrary (.top (← takeNat n)) (.put .randomCreature howPut pnote) rwho
    | .top n, .returnToHand .artifact hnote =>
      return .revealLibrary (.top (← takeNat n)) (.returnToHand .artifact hnote) rwho
    | .top n, .returnToHand (.milledSubtype s) hnote =>
      return .revealLibrary (.top (← takeNat n)) (.returnToHand (.milledSubtype (← takeStr s)) hnote) rwho
    | .top n, .returnToHand .twoPiles hnote =>
      return .revealLibrary (.top (← takeNat n)) (.returnToHand .twoPiles hnote) rwho
    | .top a, .sequence [.put .landsYouControl .tapped pnote, .gainLife (.fixed b) lwho] =>
      return .revealLibrary (.top (← takeNat a))
        (.sequence [.put .landsYouControl .tapped pnote, .gainLife (.fixed (← takeNat b.toNat)) lwho]) rwho
    | .top n, .put .creaturesYouControl howPut pnote =>
      return .revealLibrary (.top (← takeNat n)) (.put .creaturesYouControl howPut pnote) rwho
    | _, _ => return r
  | r => return r

def takeResolutionMay (action follow : @& Resolution) (how : @& TriggeredAbility.TriggerMayWhen)
    (recurse : Resolution → ArgM Resolution) : ArgM Resolution := do
  match action, follow, how with
  | .draw (.perControlled ty), .draw (.fixed 1) .eachOpponent, .ifYouDo =>
    return .may (.draw (.perControlled (← takeCardType ty))) (.draw (.fixed 1) .eachOpponent) .ifYouDo
  | .put (.creatureFromHand s n), .draw (.fixed 1), .ifYouDont =>
    let n ← takeNat n
    let s ← takeStr s
    return .may (.put (.creatureFromHand s n)) (.draw (.fixed 1)) .ifYouDont
  | .pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card]), .draw (.fixed n), .ifYouDo =>
    return .may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card])) (.draw (.fixed (← takeNat n.toNat))) .ifYouDo
  | .discard (.cards 1), .draw (.fixed n), .ifYouDo =>
    return .may (.discard (.cards 1)) (.draw (← takeNat n.toNat)) .ifYouDo
  | .pay (.mana symbols), thenDo, .ifYouDo =>
    match symbols.toList with
    | [.generic n] =>
      return .may (.pay (.mana #[.generic (← takeNat n)])) thenDo .ifYouDo
    | _ => return .may (.pay (.mana symbols)) thenDo .ifYouDo
  | .pay (.sacrifice (.fixed 1) .anotherCreatureOrArtifact), thenDo, .ifYouDo =>
    return .may (.pay (.sacrifice (.fixed 1) .anotherCreatureOrArtifact)) thenDo .ifYouDo
  | r, thenDo, how => return .may (← recurse r) (← recurse thenDo) how

def takeResolutionSequence (rs : @& List Resolution)
    (recurse : Resolution → ArgM Resolution) : ArgM Resolution := do
  match rs with
  | [.pump (.fixed p) (.fixed t) (.intersection [.creaturesYouControl, .union what]),
     .pump (.fixed op) (.fixed ot) .opponentsCreatures] =>
    let ss := (what.filterMap fun | .othersOfSubtype s => some s | _ => none).toArray
    let ss ← takeStrs ss
    let p ← takeInt p
    let t ← takeInt t
    let op ← takeInt op
    let ot ← takeInt ot
    return .sequence
      [.pump (.fixed p) (.fixed t) (.intersection [.creaturesYouControl, .union (ss.toList.map .othersOfSubtype)]),
       .pump (.fixed op) (.fixed ot) .opponentsCreatures]
  | [.putCounters (.ofKind .plan 1) .source, .loseLife (.fixed n) .eachOpponent, .gainLife (.fixed _) .you] =>
    let n ← takeNat n.toNat
    return .sequence [.putCounters (.ofKind .plan 1) .source, .loseLife (.fixed n) .eachOpponent, .gainLife (.fixed n) .you]
  | [.gainLife (.fixed n) .player, .searchLibrary (.put .basicLand .asPrinted pnote), .putCounters (.ofKind .plusOnePlusOne 1) .target] =>
    return .sequence [.gainLife (.fixed (← takeNat n.toNat)) .player, .searchLibrary (.put .basicLand .asPrinted pnote), .putCounters (.ofKind .plusOnePlusOne 1) .target]
  | rs => return .sequence (← rs.mapM recurse)

def takeResolutionModes (r : @& Resolution) (modes : @& List Resolution) (how : @& TriggeredAbility.TriggerModeHow)
    (recurse : Resolution → ArgM Resolution) : ArgM Resolution := do
  match modes, how with
  | [sub], .unlessPays n => return .unlessPays (← recurse sub) (← takeNat n)
  | rs, .one => return .or (← rs.mapM recurse)
  | [sub], .«if» cond =>
    if let .draw (.fixed 1) who := sub then
      if let .or [.attackedWithSubtype s, .subtypeEntered _] := cond then
        let s ← takeStr s
        return .«if» (.or [.attackedWithSubtype s, .subtypeEntered s]) (.draw (.fixed 1) who)
    if let .grant (.keywords kw) .target := sub then
      if cond == .teamwork then
        let name ← takeStr kw.joinedAnd
        let kw := (Keywords.ofName? name).getD kw
        return .«if» .teamwork (.grant (.keywords kw) .target)
    let sub ← recurse sub
    match cond with
    | .subtype s => return .«if» (.subtype (← takeStr s)) sub
    | .dealtDamageToSubtype s => return .«if» (.dealtDamageToSubtype (← takeStr s)) sub
    | .mvAtMost n => return .«if» (.mvAtMost (← takeNat n)) sub
    | .castFromGraveyard => return .«if» .castFromGraveyard sub
    | .teamwork => return .«if» .teamwork sub
    | .giftPromised => return .«if» .giftPromised sub
    | _ => return .«if» cond sub
  | [whenTrue, whenFalse], .ifElse cond =>
    let whenFalse ← recurse whenFalse
    let cond ← match cond with
      | .subtype s => do
        let s ← takeStr s
        pure (.subtype s)
      | .mvAtMost n => do
        let n ← takeNat n
        pure (.mvAtMost n)
      | .castFromGraveyard => pure .castFromGraveyard
      | .teamwork => pure .teamwork
      | .giftPromised => pure .giftPromised
      | c => pure c
    let whenTrue ← recurse whenTrue
    return .ifElse cond whenTrue whenFalse
  | _, _ => return r

partial def takeResolution (r : @& Resolution) : ArgM Resolution := do
  match r with
  | .grant what who => takeResolutionGrant r what who
  | .combatCountersOrTokens none (some _) ..
  | .combatCountersOrTokens none none none none none .. => takeResolutionCombat r
  | .combatCountersOrTokens .. => takeResolutionTokensOrCounters r
  | .playerResource .. => takeResolutionPlayerResource r
  | .zoneOrTap true .. => takeResolutionTapDiscardOrReturn r
  | .zoneOrTap false .. => takeResolutionPutExileOrDestroy r
  | .queueReflexive sub => return .queueReflexive (← takeResolution sub)
  | .flowOrReveal false none (some _) .. => takeResolutionRevealLibrary r
  | .may action follow how => takeResolutionMay action follow how takeResolution
  | .sequence rs => takeResolutionSequence rs takeResolution
  | .chooseModes modes how => takeResolutionModes r modes how takeResolution
  | r => return r

def isCanonicalDestroy (e : Effect) : Bool :=
  e.resolution == .destroy .target &&
    e.events.isEmpty && !e.allowsZeroTargets && !e.phrase.isEmpty &&
    match e.targeting.kind with
    | .filtered _ | .oppArtifact => false
    | _ => true

def takeEffect (e : Effect) : ArgM Effect := do
  match e.resolution with
  | .put (.nonlandMvAtMost n) _ _ =>
    return SharedTrigger.putNonlandMvAtMostFromGy (← takeNat n)
  | .destroy .target =>
    if isCanonicalDestroy e || !e.events.isEmpty then
      let kind ← takeWholeKind e.targeting.kind
      return { e with targeting := { e.targeting with kind } }
    else takeEffectRest e
  | .putCounters (.ofKind .plusOnePlusOne n) .permanent =>
    if e.events.isEmpty && !e.phrase.isEmpty then
      match e.targeting.kind with
      | .creatureYouControl | .creatureYouControlAnySubtype _ =>
        let kind ← takeWholeKind e.targeting.kind
        let n ← takeNat n
        return { e with
          targeting := { e.targeting with kind }
          resolution := .putCounters (.ofKind .plusOnePlusOne n) .permanent }
      | _ => takeEffectRest e
    else takeEffectRest e
  | _ => takeEffectRest e
where
  takeEffectRest (e : Effect) : ArgM Effect := do
    let targeting ← takeTargeting e.targeting
    let resolution ←
      match targeting.kind, e.resolution with
      | .creatureCardInYourGraveyardMvAtMost n, .put (.creatureMvAtMost _) how note =>
        pure (.put (.creatureMvAtMost n) how note)
      | _, r => takeResolution r
    let dividedDamage ←
      match e.dividedDamage with
      | some (a, b) => pure (some (← takeNat a, ← takeNat b))
      | none => pure none
    let maxTargets ← if e.maxTargets == 0 then pure e.maxTargets else takeNat e.maxTargets
    return { e with targeting, resolution, dividedDamage, maxTargets }

def takeStatic (ab : @& StaticAbility) : ArgM StaticAbility := do
  match ab with
  | .otherCreaturesHaveTrample ss =>
    if ss.isEmpty then return .otherCreaturesHaveTrample #[]
    else return .otherCreaturesHaveTrample (← takeStrs ss)
  | .pt (.creaturesYouControlGet p t ss otherOnly) =>
    let ss ← takeStrs ss
    return .pt (.creaturesYouControlGet (← takeInt p) (← takeInt t) ss otherOnly)
  | .enchantedCreatureGets p t => return .enchantedCreatureGets (← takeInt p) (← takeInt t)
  | .equippedCreatureGets p t => return .equippedCreatureGets (← takeInt p) (← takeInt t)
  | .cantBlockUnlessYouControl ss => return .cantBlockUnlessYouControl (← takeStrs ss)
  | .combat (.cantBeBlockedCount n maxBlockers) =>
    return .combat (.cantBeBlockedCount (← takeNat n) maxBlockers)
  | .enchantedIsOnlySubtypeCantAttackOrBlock s =>
    return .enchantedIsOnlySubtypeCantAttackOrBlock (← takeStr s)
  | .pt (.attachedCreatureGetsAndHas eq p t k w) =>
    if p == 0 && t == 0 then
      let w ← if w == 0 then pure 0 else takeNat w
      return .pt (.attachedCreatureGetsAndHas eq 0 0 k w)
    else
      let p ← takeInt p
      let t ← takeInt t
      let w ← if w == 0 then pure 0 else takeNat w
      return .pt (.attachedCreatureGetsAndHas eq p t k w)
  | .ability (.keywordIfYouControlOtherSubtype k s) =>
    return .ability (.keywordIfYouControlOtherSubtype k (← takeStr s))
  | .cantAttackUnlessYouControlNOther n s =>
    return .cantAttackUnlessYouControlNOther (← takeNat n) (← takeStr s)
  | .pt (.legendaryOrNonlegendaryCreaturesGet p t legendary w) =>
    let p ← takeInt p
    let t ← takeInt t
    let w ← if legendary then takeNat w else pure 0
    return .pt (.legendaryOrNonlegendaryCreaturesGet p t legendary w)
  | .pt (.thresholdGets p t k) =>
    if k == Keywords.none then return .thresholdGets (← takeInt p) (← takeInt t)
    else return ab
  | .combat (.cantBeBlockedByPower n atLeast) =>
    return .combat (.cantBeBlockedByPower (← takeInt n) atLeast)
  | .pt (.getsIfEnduringStory p t k team) =>
    return .pt (.getsIfEnduringStory (← takeInt p) (← takeInt t) k team)
  | .artifactsAndCreaturesHaveWardIfEnduringStory n =>
    return .artifactsAndCreaturesHaveWardIfEnduringStory (← takeNat n)
  | .creaturesCantAttackYouUnlessPayIfEnduringStory n =>
    return .creaturesCantAttackYouUnlessPayIfEnduringStory (← takeNat n)
  | .otherSubtypeHaveTapAddOneOf ss m =>
    return .otherSubtypeHaveTapAddOneOf (← takeStrs ss) m
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
  | .youAndOtherSubtypeHaveHexproofIfShield s =>
    return .youAndOtherSubtypeHaveHexproofIfShield (← takeStr s)
  | .subtypeSpellsCostLess s n => return .subtypeSpellsCostLess (← takeStr s) (← takeNat n)
  | .cantBeBlockedIfPowerAtMost n => return .cantBeBlockedIfPowerAtMost (← takeInt n)
  | .rule (.maximumHandSize n) =>
    if n == 0 then return .noMaximumHandSize else return .maximumHandSize (← takeNat n)
  | .powerEqualSubtypeYouControl s => return .powerEqualSubtypeYouControl (← takeStr s)
  | .typeSpellsCostLess ty n =>
    return .typeSpellsCostLess (← takeCardType ty) (← takeNat n)
  | .supertypeSpellsCostLess s n =>
    return .supertypeSpellsCostLess (← takeSupertype s) (← takeNat n)
  | .wardDiscardOrPay n => return .wardDiscardOrPay (← takeNat n)
  | .wardPoisonCounters n => return .wardPoisonCounters (← takeNat n)
  | .otherPowerUpCostsLess n => return .otherPowerUpCostsLess (← takeNat n)
  | .opponentsCreaturesGet p t => return .opponentsCreaturesGet (← takeInt p) (← takeInt t)
  | .pt (.getsPowerPerControlled p attachedEquipment) =>
    return .pt (.getsPowerPerControlled (← takeInt p) attachedEquipment)
  | .getsIfGyCreatureCards n p t =>
    return .getsIfGyCreatureCards (← takeNat n) (← takeInt p) (← takeInt t)
  | .enchantedCreatureGetsHasAndTypes p t k ts =>
    return .enchantedCreatureGetsHasAndTypes (← takeInt p) (← takeInt t) k (← takeStrs ts)
  | .getsAndAllTypesIfGyCreatureCards n p t =>
    return .getsAndAllTypesIfGyCreatureCards (← takeNat n) (← takeInt p) (← takeInt t)
  | .sneak c => return .sneak (← takeCost c)
  | ab => return ab

def takeCostPick (p : CostPick) : ArgM CostPick := do
  match p with
  | .sacrificeAnotherSubtype s => return .sacrificeAnotherSubtype (← takeStr s)
  | p => return p

def takeCostFields (c : ActivationCost) : ArgM ActivationCost := do
  let mana ← takeCost c.mana
  let payLife ← if c.payLife == 0 then pure c.payLife else takeNat c.payLife
  let picks ← c.picks.mapM takeCostPick
  return { c with mana, payLife, picks }

def takeActivationCondition (c : ActivationCondition) : ArgM ActivationCondition := do
  match c with
  | .youControlCreatureToughnessAtLeast n =>
    return .youControlCreatureToughnessAtLeast (← takeNat n)
  | .gyCreaturesAtLeast n =>
    return .gyCreaturesAtLeast (← takeNat n)
  | c => return c

def takeActivationCostReduction : ActivationCostReduction → ArgM ActivationCostReduction
  | .ifYouControlLegendary n => return .ifYouControlLegendary (← takeNat n)
  | .perEquipment n => return .perEquipment (← takeNat n)
  | .ifTargetPowerAtMost n p => return .ifTargetPowerAtMost (← takeNat n) (← takeInt p)
  | r => pure r

def takeEquipRestriction : EquipRestriction → ArgM EquipRestriction
  | .subtype s => return .subtype (← takeStr s)
  | r => pure r

def takeActivated (ab : ActivatedAbility) : ArgM ActivatedAbility := do
  let cost ← takeCostFields ab.cost
  let effect ← takeEffect ab.effect
  let otherModes ← ab.otherModes.mapM takeEffect
  let costReduction ← takeActivationCostReduction ab.costReduction
  let equipRestriction ← takeEquipRestriction ab.equipRestriction
  let condition ← takeActivationCondition ab.condition
  return { ab with
    cost, effect, otherModes, costReduction, equipRestriction, condition }

def takeInterveningCondition : InterveningCondition → ArgM InterveningCondition
  | .youControlCreatureWithPower n => return .youControlCreatureWithPower (← takeInt n)
  | .gainedLifeAtLeast n => return .gainedLifeAtLeast (← takeNat n)
  | .anotherCreaturePowerAtMost n => return .anotherCreaturePowerAtMost (← takeInt n)
  | c => pure c

def takeOpts (o : SharedTriggerOpts) : ArgM SharedTriggerOpts := do
  return { o with
    condition := ← takeInterveningCondition o.condition
    subtype := ← takeOptStr o.subtype }

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
  | some (SlotVal.nat n) => n
  | _ => 0

def slotInt (vals : Array SlotVal) (i : Nat) : Int :=
  match vals[i]? with
  | some (SlotVal.int n) => n
  | some (SlotVal.nat n) => n
  | _ => 0

def slotStr (vals : Array SlotVal) (i : Nat) : String :=
  match vals[i]? with
  | some (SlotVal.str s) => s
  | _ => ""

def slotTy (vals : Array SlotVal) (i : Nat) : CardType :=
  match vals[i]? with
  | some (SlotVal.ty t) => t
  | _ => default

def slotSup (vals : Array SlotVal) (i : Nat) : Supertype :=
  match vals[i]? with
  | some (SlotVal.sup s) => s
  | _ => default

def slotTarget (vals : Array SlotVal) (i : Nat) : EffectTargetKind :=
  match vals[i]? with
  | some (SlotVal.kind k) => k
  | _ => .none

def slotCounter (vals : Array SlotVal) (i : Nat) : CounterKind :=
  match vals[i]? with
  | some (SlotVal.ctr k) => k
  | _ => .plusOnePlusOne

/-- True when slot `i` is the count immediately after a counter kind.
`takeCounter` then `takeNat` lands in that order after `runCollect` reverses. -/
def isCounterCount (args : Array SlotVal) (i : Nat) : Bool :=
  i > 0 &&
    match args[i - 1]? with
    | some (SlotVal.ctr _) => true
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
  | _ => timesPhrase n

def renderInt (fmt : IntFmt) (i : Int) : String :=
  match fmt with
  | .signed => signedStat i
  | _ => toString i

def renderStr (fmt : StrFmt) (s : String) : String :=
  match fmt with
  | .word _ | .sub => s
  | .plural | .subPlural => StaticAbility.pluralSubtype s
  | .cycling _ => s ++ "cycling"
  | _ => "non-" ++ s

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
    | _ => []
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
          match setSlot vals i (SlotVal.nat 1) seen with
          | some (vals, seen) => go ps ts vals seen
          | none => none
        | n :: "card" :: ts =>
          match parseNatTok n with
          | some k =>
            match setSlot vals i (SlotVal.nat k) seen with
            | some (vals, seen) => go ps ts vals seen
            | none => none
          | none => none
        | n :: "cards" :: ts =>
          match parseNatTok n with
          | some k =>
            match setSlot vals i (SlotVal.nat k) seen with
            | some (vals, seen) => go ps ts vals seen
            | none => none
          | none => none
        | _ => none
      | .counters =>
        match toks with
        | "a" :: "+1/+1" :: "counter" :: ts =>
          match setSlot vals i (SlotVal.nat 1) seen with
          | some (vals, seen) => go ps ts vals seen
          | none => none
        | n :: "+1/+1" :: "counter" :: ts =>
          match parseNatTok n with
          | some k =>
            match setSlot vals i (SlotVal.nat k) seen with
            | some (vals, seen) => go ps ts vals seen
            | none => none
          | none => none
        | n :: "+1/+1" :: "counters" :: ts =>
          match parseNatTok n with
          | some k =>
            match setSlot vals i (SlotVal.nat k) seen with
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
              match setSlot vals i (SlotVal.nat k) seen with
              | some (vals, seen) => go ps ts vals seen
              | none => none
            | none => none
          else none
        | [] => none
      | .times =>
        match toks with
        | "twice" :: ts =>
          match setSlot vals i (SlotVal.nat 2) seen with
          | some (vals, seen) => go ps ts vals seen
          | none => none
        | t :: "times" :: ts =>
          match parseNatTok t with
          | some k =>
            match setSlot vals i (SlotVal.nat k) seen with
            | some (vals, seen) => go ps ts vals seen
            | none => none
          | none => none
        | _ => none
      | _ =>
        match toks with
        | t :: ts =>
          match parseNatTok t with
          | some k =>
            match setSlot vals i (SlotVal.nat k) seen with
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
            | _ => true
          if ok then
            match setSlot vals i (SlotVal.int k) seen with
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
          match setSlot vals i (SlotVal.str (build got)) seen with
          | some (vals, seen) => some (vals, toks.drop n, seen)
          | none => none
      let takeKnown (found : Option (String × Nat)) : Option (Array SlotVal × List Nat) :=
        match found with
        | some (name, n) =>
          match setSlot vals i (SlotVal.str name) seen with
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
          match setSlot vals i (SlotVal.str (singularize t)) seen with
          | some (vals, seen) => go ps ts vals seen
          | none => none
        | [] => none
      | .cycling n =>
        match matchCyclingSubtype toks with
        | some (name, w) =>
          match setSlot vals i (SlotVal.str name) seen with
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
      | _ =>
        match matchNonSubtype toks with
        | some (name, n) =>
          match setSlot vals i (SlotVal.str name) seen with
          | some (vals, seen) => go ps (toks.drop n) vals seen
          | none => none
        | none =>
          match toks with
          | t :: ts =>
            if t.startsWith "non-" then
              match setSlot vals i (SlotVal.str (capFirst (t.drop "non-".length).toString)) seen with
              | some (vals, seen) => go ps ts vals seen
              | none => none
            else none
          | [] => none
    | .ty i :: ps =>
      match toks with
      | t :: ts =>
        match CardType.ofOracle? t with
        | some ty =>
          match setSlot vals i (SlotVal.ty ty) seen with
          | some (vals, seen) => go ps ts vals seen
          | none => none
        | none => none
      | [] => none
    | .sup i :: ps =>
      match toks with
      | t :: ts =>
        match Supertype.ofOracle? t with
        | some sup =>
          match setSlot vals i (SlotVal.sup sup) seen with
          | some (vals, seen) => go ps ts vals seen
          | none => none
        | none => none
      | [] => none
    | .kind i :: ps =>
      match fromNounPrefix toks with
      | some (k, n) =>
        match setSlot vals i (SlotVal.kind k) seen with
        | some (vals, seen) => go ps (toks.drop n) vals seen
        | none => none
      | none => none
    | .counterPhrase ni ki :: ps =>
      match CounterKind.matchPhrase toks with
      | some (n, k, w) =>
        match setSlot vals ni (SlotVal.nat n) seen with
        | none => none
        | some (vals, seen) =>
          match setSlot vals ki (SlotVal.ctr k) seen with
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
              match setSlot vals i (SlotVal.int p) seen with
              | none => none
              | some (vals, seen) =>
                match setSlot vals j (SlotVal.int q) seen with
                | some (vals, seen) => go ps ts vals seen
                | none => none
            else none
          | _, _ => none
        | _ => none
      | [] => none
    | _ => none
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
      | _ => "#x"
    | .int _ fmt =>
      match fmt with
      | .signed => "#+"
      | _ => "#i"
    | .str _ fmt =>
      match fmt with
      | .word n => s!"$w{n}"
      | .plural => "$p"
      | .cycling n => s!"$c{n}"
      | .non => "$n"
      | .sub => "$s"
      | _ => "$sp"
    | .ty _ => "$t"
    | .sup _ => "$sup"
    | .kind _ => "$k"
    | .pt _ _ signed => if signed then "+/+" else "#/#"
    | .counterPhrase _ _ => "#ctr"
    | _ => ""
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
  | _ => ""

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
  if isCanonicalDestroy new then
    Effect.canonicalDestroy new.targeting.kind
  else
    match new.resolution with
    | .putCounters (.ofKind .plusOnePlusOne n) .permanent =>
      if new.events.isEmpty && !new.phrase.isEmpty then
        match Effect.canonicalPlusOne n new.targeting.kind with
        | some e => e
        | none => { new with phrase := splicePhrase old.phrase oldArgs newArgs }
      else { new with phrase := splicePhrase old.phrase oldArgs newArgs }
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

#guard
  let ab := TriggeredAbility.onEnterExileOppGyCardOppsLoseLife 2
  refillTriggered ab (collectTriggered ab) == ab
#guard
  let ab := TriggeredAbility.onCastNoncreaturePumpAndDamageOpponents 1
  refillTriggered ab (collectTriggered ab) == ab
#guard
  let ab := TriggeredAbility.onEnterUntapOtherPlusOneIfSubtype "Bear"
  refillTriggered ab (collectTriggered ab) == ab
#guard
  let ab := TriggeredAbility.onPlayerCastsSecondSpellLoseLifeCreateTreasure
  refillTriggered ab (collectTriggered ab) == ab

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
      (.spellsCostLess (.cardType .planeswalker) (.fixed 3))
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
  some ((.amass 4 "Zombie"))

#guard refilled (Effect.riddlesInTheDark) "look at the top six cards of your library and separate them into a face-down pile and a face-up pile. An opponent chooses one of the piles. Put that pile into your hand and the other into your graveyard" ==
  some (.revealLibrary (.top 6) (.returnToHand .twoPiles))

#guard refilled (Effect.plusOneOnEachYouControl) "put 3 +1/+1 counters on each creature you control" ==
  some ((.putCounters (.ofKind .plusOnePlusOne 3) .youControl))

#guard Effect.plusOneThenEachOtherIfFromGy.phrase ==
  "put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control"

#guard refilled Effect.plusOneThenEachOtherIfFromGy
    "Put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control." ==
  some Effect.plusOneThenEachOtherIfFromGy.resolution

#guard refilled Effect.plusOneThenEachOtherIfFromGy
    "Put 2 +1/+1 counters on target creature you control. If this spell was cast from a graveyard, also put 3 +1/+1 counters on each other creature you control." ==
  some (.sequence [
    (.putCounters (.ofKind .plusOnePlusOne 2) .firstTargetCreatureYouControl),
    (.«if» .castFromGraveyard (.putCounters (.ofKind .plusOnePlusOne 3) .eachOther))])

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
  some (.dealDamage (.fixed 5) (.nonSubtypeCreatures "Elf"))

#guard refilled (Effect.searchLegendaryCreatureToHand)
    "search your library for a basic land card, reveal it, put it into your hand, then shuffle" ==
  some (.searchLibrary (.returnToHand (.supertypeCard .basic .land)))

#guard refilled (Effect.creatureYouControlDealsTwicePower)
    "Target creature you control deals damage equal to 3 times its power to target creature an opponent controls." ==
  some ((.fight .announced (.timesPower 3)))

#guard refilled (Effect.drawThreeDiscardUnlessArtifact)
    "draw three cards. Then discard four cards unless you discard an enchantment card" ==
  some (.sequence [.draw 3, (.discard (.cardsUnlessType 4 .enchantment))])

#guard refilled (Effect.becomeArtifactCreature44Flying)
    "until end of turn, target artifact or creature you control becomes an artifact creature with base power and toughness 2/3 and gains haste" ==
  some ((.grant (.artifactCreature 2 3 "Haste") .target))

#guard refilled (Effect.mayDrawPerArtifactOppsDraw)
    "You may draw a card for each creature you control. If you do, each opponent draws a card" ==
  some ((.may (.draw (.perControlled .creature)) (.draw (.fixed 1) (who := .eachOpponent)) .ifYouDo))

#guard refilled (Effect.addRedPerOppArtifacts)
    "add {R} for each enchantment your opponents control" ==
  some (.addMana #[.colored .red] (.count (.oppPermanents .enchantment)))

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
      (.spellsCostLess (.supertype s) (.fixed 3))
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
      (.ifElse .castFromGraveyard (.amass 4 "Zombie") (.amass 2 "Zombie"))
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
