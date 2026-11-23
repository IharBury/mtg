import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.ChapterEffects
import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.OracleNorm
import Mtg.Engine.Card.Parser.SubGrammars
import Mtg.Engine.Card.TriggeredAbility

/-!
Argument values in modeled Oracle text.

A candidate ability is a shape. `Nat`, `Int`, `String`, and `TargetSpec`
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
  /-- The whole target specification (`target creature`, `target artifact token`, …). -/
  | targets (ts : TargetSpec)
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

def takeSubtype (sub : CardSubtype) : ArgM CardSubtype := do
  let s ← takeStr sub.englishName
  return CardSubtype.ofOracleD s sub

def takeSubtypes (xs : Array CardSubtype) : ArgM (Array CardSubtype) :=
  xs.mapM takeSubtype

def takeCardTypes (xs : Array CardType) : ArgM (Array CardType) :=
  xs.mapM takeCardType

def takeOptSubtype (o : Option CardSubtype) : ArgM (Option CardSubtype) :=
  match o with
  | none => pure none
  | some sub => return some (← takeSubtype sub)

def takeSymbol (s : ManaSymbol) : ArgM ManaSymbol :=
  match s with
  | .generic n => return .generic (← takeNat n)
  | s => return s

def takeCost (c : ManaCost) : ArgM ManaCost := do
  return { symbols := ← c.symbols.mapM takeSymbol }

/-- One slot for the whole target specification, noun included.
Nested numbers stay inside the `TargetSpec` instead of becoming their own holes. -/
def takeWholeTargetSpec (ts : TargetSpec) : ArgM TargetSpec := do
  let s ← get
  match s.mode with
  | .collect =>
    set { s with vals := .targets ts :: s.vals }
    return ts
  | .fill =>
    match s.vals with
    | .targets v :: rest =>
      set { s with vals := rest }
      return v
    | _ => return ts

private partial def takeTargetObjectPred (pred : ObjectPred) : ArgM ObjectPred := do
  if pred == ObjectPred.worthy then return pred
  match pred with
  | .all ps => return .all (← ps.mapM takeTargetObjectPred)
  | .any ps =>
    -- Paired `"power or toughness N or less"` takes a single `Nat` slot.
    if ps.size == 2 then
      match ps[0]!, ps[1]! with
      | .stat .power op1 (.const v1), .stat .toughness op2 (.const v2) =>
        if op1 == op2 && v1 == v2 && v1 >= 0 then
          let n ← takeNat v1.toNat
          return .any #[.stat .power op1 (.const (Int.ofNat n)), .stat .toughness op2 (.const (Int.ofNat n))]
        else
          return .any (← ps.mapM takeTargetObjectPred)
      | _, _ => return .any (← ps.mapM takeTargetObjectPred)
    else
      return .any (← ps.mapM takeTargetObjectPred)
  | .not p => return .not (← takeTargetObjectPred p)
  | .stat .manaValue op (.const v) =>
    if v >= 0 then
      let n ← takeNat v.toNat
      return .stat .manaValue op (.const (Int.ofNat n))
    else
      return .stat .manaValue op (.const v)
  | .stat k op (.const v) =>
    return .stat k op (.const (← takeInt v))
  | other => return other

private partial def takeTargetDomain (d : TargetDomain) : ArgM TargetDomain := do
  match d with
  | .object zs pred => return .object zs (← takeTargetObjectPred pred)
  | .anyOf ds => return .anyOf (← ds.mapM takeTargetDomain)
  | other => return other

private def takeGroupConstraint (gc : GroupTargetConstraint) : ArgM GroupTargetConstraint := do
  match gc with
  | .totalManaValueAtMost (.const v) =>
    if v >= 0 then
      let n ← takeNat v.toNat
      return .totalManaValueAtMost (.const (Int.ofNat n))
    else
      return gc
  | other => return other

private def takeTargetSlot (slot : TargetSlot) : ArgM TargetSlot := do
  let domain ← takeTargetDomain slot.domain
  let groupConstraint? ←
    match slot.groupConstraint? with
    | some gc => pure (some (← takeGroupConstraint gc))
    | none => pure none
  return { slot with domain, groupConstraint? }

/-- Compositional argument walker over `TargetSpec` (subtypes on bare creature-you-control
slots plus numeric thresholds inside `ObjectPred` and `GroupTargetConstraint`). -/
def takeTargetSpec (ts : TargetSpec) : ArgM TargetSpec := do
  if let some s := ts.creatureYouControlSubtype? then
    return .creatureYouControlSubtype (← takeSubtype s)
  else if let some ss := ts.creatureYouControlAnySubtype? then
    return .creatureYouControlAnySubtype (← takeSubtypes ss)
  else
    return { ts with slots := ← ts.slots.mapM takeTargetSlot }

private partial def takeTriggerCond (c : Condition) : ArgM Condition := do
  match c with
  | .exists (.inZones zs (.all #[.hasType .creature, .controlledBy pf, .stat .power .ge (.const n)])) =>
    return .exists (.inZones zs (.all #[.hasType .creature, .controlledBy pf, .stat .power .ge (.const (← takeInt n))]))
  | .cmp .ge (.playerMetric .lifeGainedThisTurn pf) (.const n) =>
    let k ← takeNat n.toNat
    return .cmp .ge (.playerMetric .lifeGainedThisTurn pf) (.const (Int.ofNat k))
  | .exists (.inZones zs (.all #[.hasSubtype (.literal s), .controlledBy pf])) =>
    return .exists (.inZones zs (.all #[.hasSubtype (.literal (← takeSubtype s)), .controlledBy pf]))
  | .exists (.inZones zs (.hasSubtype (.literal s))) =>
    return .exists (.inZones zs (.hasSubtype (.literal (← takeSubtype s))))
  | .playerPred who (.controls { zones, pred := .hasSubtype (.literal s) } cnt) =>
    return .playerPred who (.controls { zones, pred := .hasSubtype (.literal (← takeSubtype s)) } cnt)
  | .exists (.filter o (.hasSubtype (.literal s))) =>
    return .exists (.filter o (.hasSubtype (.literal (← takeSubtype s))))
  | .exists (.filter o (.stat .manaValue .le (.const n))) =>
    return .exists (.filter o (.stat .manaValue .le (.const (Int.ofNat (← takeNat n.toNat)))))
  | .cmp op (.objectStat stat obj) (.const n) =>
    return .cmp op (.objectStat stat obj) (.const (Int.ofNat (← takeNat n.toNat)))
  | .any #[
      .turnHistory (.eventOccurredThisTurn pf1 (.attackedWith (.hasSubtype (.literal s)) n)),
      .turnHistory (.eventOccurredThisTurn pf2 (.permanentEntered (.hasSubtype (.literal _))))] =>
    let s' ← takeSubtype s
    return .any #[
      .turnHistory (.eventOccurredThisTurn pf1 (.attackedWith (.hasSubtype (.literal s')) n)),
      .turnHistory (.eventOccurredThisTurn pf2 (.permanentEntered (.hasSubtype (.literal s'))))]
  | other => return other

private partial def takeTriggerPattern (p : TriggerPattern) : ArgM TriggerPattern := do
  match p with
  | .or a b => return .or (← takeTriggerPattern a) (← takeTriggerPattern b)
  | .whenCond inner c => return .whenCond (← takeTriggerPattern inner) (← takeTriggerCond c)
  | .zoneChange subj fromZ toZ mby? cc? =>
    let subj' ←
      match subj with
      | .any #[.sameAs .this, .all #[.hasSubtype (.literal s), .controlledBy pf]] =>
        pure (.any #[.sameAs .this, .all #[.hasSubtype (.literal (← takeSubtype s)), .controlledBy pf]])
      | .any #[.sameAs .this, .all #[.isToken false, .hasSubtype (.literal s), .controlledBy pf]] =>
        pure (.any #[.sameAs .this, .all #[.isToken false, .hasSubtype (.literal (← takeSubtype s)), .controlledBy pf]])
      | .all #[.otherThan .this, .controlledBy pf,
          .any #[.hasSubtype (.literal s), .all #[.hasType .artifact, .hasSubtype (.literal .equipment)]]] =>
        pure (.all #[.otherThan .this, .controlledBy pf,
          .any #[.hasSubtype (.literal (← takeSubtype s)), .all #[.hasType .artifact, .hasSubtype (.literal .equipment)]]])
      | .all #[.otherThan .this, .hasType .creature, .controlledBy pf, .stat .power .le (.const n)] =>
        pure (.all #[.otherThan .this, .hasType .creature, .controlledBy pf, .stat .power .le (.const (← takeInt n))])
      | .all #[.otherThan .this, .hasSupertype .legendary, .hasSubtype (.literal s), .controlledBy pf] =>
        pure (.all #[.otherThan .this, .hasSupertype .legendary, .hasSubtype (.literal (← takeSubtype s)), .controlledBy pf])
      | .all #[.otherThan .this, .hasSubtype (.literal s), .controlledBy pf] =>
        pure (.all #[.otherThan .this, .hasSubtype (.literal (← takeSubtype s)), .controlledBy pf])
      | .all #[.hasSubtype (.literal s), .controlledBy pf] =>
        if s == .forest || s == .mountain then pure subj
        else pure (.all #[.hasSubtype (.literal (← takeSubtype s)), .controlledBy pf])
      | other => pure other
    return .zoneChange subj' fromZ toZ mby? cc?
  | .attacks subj atkDef alone minC (some n) only =>
    return .attacks subj atkDef alone minC (some (← takeInt n)) only
  | .damageDealt (.all #[.hasSubtype (.literal s), .controlledBy pf]) recip combat noncombat =>
    return .damageDealt (.all #[.hasSubtype (.literal (← takeSubtype s)), .controlledBy pf]) recip combat noncombat
  | other => return other

private def takeTriggerGrouping (g : BatchGrouping) : ArgM BatchGrouping := do
  match g with
  | .counterThreshold .plan #[n] => return .counterThreshold .plan #[← takeNat n]
  | other => return other

private def takeSubPredArray (ps : Array ObjectPred) : ArgM (Array ObjectPred) := do
  let subs := ps.filterMap fun | .hasSubtype (.literal s) => some s | _ => none
  if !subs.isEmpty && subs.size == ps.size then
    let subs' ← takeSubtypes subs
    return subs'.map fun s => .hasSubtype (.literal s)
  else return ps

private def takeInstrContMod : ContinuousModification → ArgM ContinuousModification
  | .modifyPT (.const p) (.const t) =>
    return .modifyPT (.const (← takeInt p)) (.const (← takeInt t))
  | .setBasePT (some (.const p)) (some (.const t)) =>
    return .setBasePT (some (.const (← takeInt p))) (some (.const (← takeInt t)))
  | .grantKeywords ks => do
    if ks.isEmpty then return .grantKeywords ks
    else
      let name ← takeStr (KeywordAbility.joinedAnd ks)
      let ks' := ((KeywordAbility.ofSimpleName? name).map (#[·])).getD ks
      return .grantKeywords ks'
  | .modifyTypes m => do
    if m.subtypes.isEmpty then return .modifyTypes m
    else return .modifyTypes { m with subtypes := ← takeSubtypes m.subtypes }
  | .all mods => return .all (← mods.attach.mapM fun ⟨m, _⟩ => takeInstrContMod m)
  | other => return other

private def takeInstrMoveMods (mods : MoveMods) : ArgM MoveMods := do
  let choice? ←
    match mods.choice? with
    | none => pure none
    | some c =>
      let count ←
        match c.count with
        | .exact (.const n) => pure (.exact (.const (Int.ofNat (← takeNat n.toNat))))
        | .upTo (.const n) => pure (.upTo (.const (Int.ofNat (← takeNat n.toNat))))
        | other => pure other
      let unlessMatching? ←
        match c.unlessMatching? with
        | some (.hasType ty) => pure (some (.hasType (← takeCardType ty)))
        | other => pure other
      let filter? ←
        match c.filter? with
        | some (.hasSubtype (.literal s)) => pure (some (.hasSubtype (.literal (← takeSubtype s))))
        | some (.stat .manaValue .le (.const n)) =>
          pure (some (.stat .manaValue .le (.const (Int.ofNat (← takeNat n.toNat)))))
        | some (.all #[.hasType .creature, .stat .manaValue .le (.const n)]) =>
          pure (some (.all #[.hasType .creature, .stat .manaValue .le (.const (Int.ofNat (← takeNat n.toNat)))]))
        | other => pure other
      pure (some { c with count, unlessMatching?, filter? })
  let grantPlayPerm? ←
    match mods.grantPlayPerm? with
    | none => pure none
    | some gp =>
      let condition? ←
        match gp.condition? with
        | some c => pure (some (← takeTriggerCond c))
        | none => pure none
      let filter? ←
        match gp.filter? with
        | some (.hasType ty) => pure (some (.hasType (← takeCardType ty)))
        | other => pure other
      pure (some { gp with condition?, filter? })
  return { mods with choice?, grantPlayPerm? }

private def takeInstrSearchFilter : ObjectPred → ArgM ObjectPred
  | .all #[.hasSupertype sup, .hasType ty] =>
    return .all #[.hasSupertype (← takeSupertype sup), .hasType (← takeCardType ty)]
  | .hasSupertype sup => do
    let name ← takeStr sup.englishName
    return Effect.searchLandTypeFilter name
  | .hasSubtype (.literal s) => do
    let name ← takeStr s.englishName
    return Effect.searchLandTypeFilter name
  | other => return other

private def takeInstrInspectFilter : ObjectPred → ArgM ObjectPred
  | .any #[.hasType a, .hasType b] =>
    return .any #[.hasType (← takeCardType a), .hasType (← takeCardType b)]
  | .hasType ty => return .hasType (← takeCardType ty)
  | .hasSubtype (.literal s) => return .hasSubtype (.literal (← takeSubtype s))
  | .isKind .permanentCard => do
    let s ← takeStr "permanent"
    return Effect.typeOrSubtypePred s
  | .any ps =>
    let subs := ps.filterMap fun | .hasSubtype (.literal s) => some s | _ => none
    if !subs.isEmpty && subs.size == ps.size then
      return .any (← takeSubPredArray ps)
    else do
      let ps' ← ps.mapM fun
        | .hasType ty => return .hasType (← takeCardType ty)
        | .hasSubtype (.literal s) => return .hasSubtype (.literal (← takeSubtype s))
        | .isKind .permanentCard => do
          let s ← takeStr "permanent"
          return Effect.typeOrSubtypePred s
        | other => return other
      return .any ps'
  | other => return other

mutual

partial def takeInstr (instr : Instruction) : ArgM Instruction := do
  match instr with
  | .moveZone objs dest verb mods =>
    let objs' ←
      match objs with
      | .topOfLibrary who (.const n) =>
        pure (.topOfLibrary who (.const (Int.ofNat (← takeNat n.toNat))))
      | .inZones zs (.hasType ty) =>
        if verb == .exile && mods.grantPlayPerm?.isSome then
          pure (.inZones zs (.hasType (← takeCardType ty)))
        else pure objs
      | .inZones zs (.all #[.hasType .creature, .stat .manaValue .le (.const n)]) =>
        pure (.inZones zs (.all #[.hasType .creature, .stat .manaValue .le (.const (Int.ofNat (← takeNat n.toNat)))]))
      | .inZones zs (.hasSubtype (.literal s)) =>
        pure (.inZones zs (.hasSubtype (.literal (← takeSubtype s))))
      | .filter inner (.hasSubtype (.literal s)) =>
        pure (.filter inner (.hasSubtype (.literal (← takeSubtype s))))
      | other => pure other
    let mods' ← takeInstrMoveMods mods
    return .moveZone objs' dest verb mods'
  | .create (.tokens who cnt spec mods) =>
    let cnt' ←
      match cnt with
      | .const n => pure (.const (Int.ofNat (← takeNat n.toNat)))
      | .aggregate .count .one (.inZones zs (.all #[.hasSubtype (.literal s), .controlledBy pf])) =>
        pure (.aggregate .count .one (.inZones zs (.all #[.hasSubtype (.literal (← takeSubtype s)), .controlledBy pf])))
      | other => pure other
    return .create (.tokens who cnt' spec mods)
  | .permanent (.modifyCounters (.put kind (.const n)) objs ch?) =>
    let kind' ← takeCounter kind
    let n' ← takeNat n.toNat
    let objs' ←
      match objs with
      | .inZones zs (.all #[.otherThan .this, .hasSubtype (.literal s), .controlledBy pf]) =>
        pure (.inZones zs (.all #[.otherThan .this, .hasSubtype (.literal (← takeSubtype s)), .controlledBy pf]))
      | .inZones zs (.all #[.hasSubtype (.literal s), .controlledBy pf]) =>
        pure (.inZones zs (.all #[.hasSubtype (.literal (← takeSubtype s)), .controlledBy pf]))
      | other => pure other
    return .permanent (.modifyCounters (.put kind' (.const (Int.ofNat n'))) objs' ch?)
  | .permanent (.modifyCounters (.remove k? (.exact (.const n))) objs ch?) =>
    return .permanent (.modifyCounters (.remove k? (.exact (.const (Int.ofNat (← takeNat n.toNat))))) objs ch?)
  | .damage (.deal src rec amt fl) =>
    let amt' ←
      match amt with
      | .const n => pure (.const (Int.ofNat (← takeNat n.toNat)))
      | .binary .mul (.const k) rhs =>
        if k == 1 then pure amt
        else pure (.binary .mul (.const (Int.ofNat (← takeNat k.toNat))) rhs)
      | .aggregate .count .one (.inZones zs (.all #[.hasSubtype (.literal s), .controlledBy pf])) =>
        pure (.aggregate .count .one (.inZones zs (.all #[.hasSubtype (.literal (← takeSubtype s)), .controlledBy pf])))
      | other => pure other
    let rec' ←
      match rec with
      | .objects (.inZones zs (.all #[.hasType .creature, .not (.hasSubtype (.literal s))])) =>
        pure (.objects (.inZones zs (.all #[.hasType .creature, .not (.hasSubtype (.literal (← takeSubtype s)))])))
      | .both (.inZones zs (.all #[.hasType .creature, .not (.hasSubtype (.literal s))])) pls =>
        pure (.both (.inZones zs (.all #[.hasType .creature, .not (.hasSubtype (.literal (← takeSubtype s)))])) pls)
      | other => pure other
    return .damage (.deal src rec' amt' fl)
  | .life (.gain who (.const n)) =>
    return .life (.gain who (.const (Int.ofNat (← takeNat n.toNat))))
  | .life (.lose who (.const n)) =>
    return .life (.lose who (.const (Int.ofNat (← takeNat n.toNat))))
  | .life (.set who (.const n)) =>
    return .life (.set who (.const (Int.ofNat (← takeNat n.toNat))))
  | .player (.drawCards who (.const n)) =>
    return .player (.drawCards who (.const (Int.ofNat (← takeNat n.toNat))))
  | .player (.drawCards who (.aggregate .count .one (.inZones zs (.all #[.hasType ty, .controlledBy pf])))) =>
    return .player (.drawCards who (.aggregate .count .one (.inZones zs (.all #[.hasType (← takeCardType ty), .controlledBy pf]))))
  | .player (.scry who (.const n)) =>
    return .player (.scry who (.const (Int.ofNat (← takeNat n.toNat))))
  | .player (.surveil who (.const n)) =>
    return .player (.surveil who (.const (Int.ofNat (← takeNat n.toNat))))
  | .player (.amass who sub (.const n)) =>
    let n' ← takeNat n.toNat
    let sub' ← takeSubtype sub
    return .player (.amass who sub' (.const (Int.ofNat n')))
  | .player (.amass who sub (.objectStat .power .this)) =>
    return .player (.amass who (← takeSubtype sub) (.objectStat .power .this))
  | .player (.empowerPlaneswalker sub (.const n)) =>
    return .player (.empowerPlaneswalker sub (.const (Int.ofNat (← takeNat n.toNat))))
  | .player (.addMana who mp) =>
    let spec' : ManaSpec ←
      match mp.spec with
      | .sequence #[(.colored c, .aggregate .count .one (.inZones zs (.all #[.hasType ty, .controlledBy pf])))] =>
        pure (ManaSpec.sequence #[(.colored c, .aggregate .count .one (.inZones zs (.all #[.hasType (← takeCardType ty), .controlledBy pf])))])
      | .combination pal (.const n) =>
        pure (ManaSpec.combination pal (.const (Int.ofNat (← takeNat n.toNat))))
      | other => pure other
    let restriction' ←
      match mp.restriction with
      | some (.onlyForSpells (.hasSubtype s) riders) =>
        pure (some (.onlyForSpells (.hasSubtype (← takeSubtype s)) riders))
      | other => pure other
    return .player (.addMana who { mp with spec := spec', restriction := restriction' })
  | .player (.searchLibrary spec) =>
    let filter' ← takeInstrSearchFilter spec.filter
    return .player (.searchLibrary { spec with filter := filter' })
  | .player (.inspectLibrary spec) =>
    let source' ←
      match spec.source with
      | .topCards who (.const n) rev =>
        pure (.topCards who (.const (Int.ofNat (← takeNat n.toNat))) rev)
      | .millCards who (.const n) =>
        pure (.millCards who (.const (Int.ofNat (← takeNat n.toNat))))
      | other => pure other
    let action' ←
      match spec.action with
      | .takeMatching flt cnt dest mods rev rand =>
        let cnt' ←
          match cnt with
          | .upTo (.const k) =>
            if k > 1 then pure (.upTo (.const (Int.ofNat (← takeNat k.toNat)))) else pure cnt
          | other => pure other
        let flt' ← takeInstrInspectFilter flt
        pure (.takeMatching flt' cnt' dest mods rev rand)
      | other => pure other
    return .player (.inspectLibrary { spec with source := source', action := action' })
  | .installEffect (.applyContinuous dur objs mod) =>
    let objs' ←
      match objs with
      | .inZones zs (.all #[.any ps, .controlledBy pf]) =>
        pure (.inZones zs (.all #[.any (← takeSubPredArray ps), .controlledBy pf]))
      | .inZones zs (.all #[.otherThan .this, .hasType .creature, .hasSubtype (.literal s), .controlledBy pf]) =>
        pure (.inZones zs (.all #[.otherThan .this, .hasType .creature, .hasSubtype (.literal (← takeSubtype s)), .controlledBy pf]))
      | .inZones zs (.all #[.otherThan .this, .hasType .creature, .any ps, .controlledBy pf]) =>
        pure (.inZones zs (.all #[.otherThan .this, .hasType .creature, .any (← takeSubPredArray ps), .controlledBy pf]))
      | .inZones zs (.all #[.otherThan .this, .hasSubtype (.literal s), .controlledBy pf]) =>
        pure (.inZones zs (.all #[.otherThan .this, .hasSubtype (.literal (← takeSubtype s)), .controlledBy pf]))
      | other => pure other
    let mod' ← takeInstrContMod mod
    return .installEffect (.applyContinuous dur objs' mod')
  | .installEffect (.applyRule dur (.costMod (.spells caster pred nth notFrom az) (.reduceGeneric (.const n)) nextOnly)) =>
    let pred' ←
      match pred with
      | .hasType ty => pure (.hasType (← takeCardType ty))
      | .hasSupertype sup => pure (.hasSupertype (← takeSupertype sup))
      | other => pure other
    let n' ← takeNat n.toNat
    return .installEffect (.applyRule dur
      (.costMod (.spells caster pred' nth notFrom az) (.reduceGeneric (.const (Int.ofNat n'))) nextOnly))
  | .stack (.copyStackObject objs (.const n) nt) =>
    return .stack (.copyStackObject objs (.const (Int.ofNat (← takeNat n.toNat))) nt)
  | .seq steps =>
    return .seq (← steps.mapM takeInstr)
  | .bind v step cont =>
    let step' ← takeInstr step
    let cont' ← takeInstr cont
    return .bind v step' cont'
  | .ifCond cond thenB elseB =>
    if elseB == .noop then
      let thenB' ← takeInstr thenB
      let cond' ← takeTriggerCond cond
      return .ifCond cond' thenB' .noop
    else
      -- Printed order is the otherwise branch, then the condition, then the true branch.
      let elseB' ← takeInstr elseB
      let cond' ← takeTriggerCond cond
      let thenB' ← takeInstr thenB
      return .ifCond cond' thenB' elseB'
  | .optional who cost? onYes onNo mt =>
    let cost?' ←
      match cost? with
      | some c =>
        match c.soleGenericMana? with
        | some n => pure (some (CostSpec.ofGeneric (← takeNat n)))
        | none => pure (some c)
      | none => pure none
    let onYes' ← takeInstr onYes
    let onNo' ← takeInstr onNo
    return .optional who cost?' onYes' onNo' mt
  | .unlessPays payer cost ifUnpaid =>
    let ifUnpaid' ← takeInstr ifUnpaid
    let cost' ←
      match cost.soleGenericMana? with
      | some n => pure (CostSpec.ofGeneric (← takeNat n))
      | none => pure cost
    return .unlessPays payer cost' ifUnpaid'
  | .chooseModes spec =>
    let modes' ← spec.modes.mapM takeEffect
    return .chooseModes { spec with modes := modes' }
  | .forEach iter v body =>
    return .forEach iter v (← takeInstr body)
  | other => return other

partial def takeEffect (e : Effect) : ArgM Effect := do
  match e.dividedDamage?, e.body with
  | some (amt, maxT), .damage (.deal src .allTargets (.const _) fl) =>
    if fl.divided then
      let amt' ← takeNat amt
      let maxT' ← takeNat maxT
      return {
        targets := TargetSpec.dividedDamage .anyTarget amt' maxT'
        body := .damage (.deal src .allTargets (.const (Int.ofNat amt')) fl) }
    else takeEffectNonDivided e
  | _, _ => takeEffectNonDivided e
where
  takeEffectNonDivided (e : Effect) : ArgM Effect := do
    if e.body == Instruction.destroy (.target 0) then
      let targets ← takeWholeTargetSpec e.targets
      return { e with targets }
    else
      match e.body with
      | .permanent (.modifyCounters (.put .plusOnePlusOne (.const n)) (.target 0) none) =>
        if e.targets == .creatureYouControl ||
            e.targets.creatureYouControlAnySubtype?.isSome then
          let targets ← takeWholeTargetSpec e.targets
          let n' ← takeNat n.toNat
          return {
            targets
            body := Instruction.putPlusOne (.target 0) n' }
        else takeEffectRest e
      | _ => takeEffectRest e
  takeEffectRest (e : Effect) : ArgM Effect := do
    let targets ← takeTargetSpec e.targets
    let body ← takeInstr e.body
    return { targets, body }

end

private def takeStaticAnySubPred : ObjectPred → ArgM ObjectPred
  | .hasSubtype (.literal s) => return .hasSubtype (.literal (← takeSubtype s))
  | .any ps => do
    let subs := ps.filterMap fun | .hasSubtype (.literal s) => some s | _ => none
    if subs.size == ps.size && !subs.isEmpty then
      let subs' ← takeSubtypes subs
      return StaticAbility.anySubtypePred subs'
    else
      let ps' ← ps.mapM fun
        | .hasSubtype (.literal s) => return .hasSubtype (.literal (← takeSubtype s))
        | .hasType t => return .hasType (← takeCardType t)
        | other => return other
      return .any ps'
  | other => return other

private def takeStaticScope (sc : ObjectFilter) : ArgM ObjectFilter := do
  match sc.zones.zones.toList, sc.pred with
  | [.battlefield], .all #[.otherThan .this, .hasType .creature, subP, .controlledBy .you] =>
    let subP' ← takeStaticAnySubPred subP
    return { sc with pred := .all #[.otherThan .this, .hasType .creature, subP', .controlledBy .you] }
  | [.battlefield], .all #[.otherThan .this, subP, .controlledBy .you] =>
    let subP' ← takeStaticAnySubPred subP
    return { sc with pred := .all #[.otherThan .this, subP', .controlledBy .you] }
  | [.battlefield], .all #[.hasType .creature, .hasSubtype (.literal s), .controlledBy .you] =>
    if s == .army then return sc
    else
      let s' ← takeSubtype s
      return { sc with pred := .all #[.hasType .creature, .hasSubtype (.literal s'), .controlledBy .you] }
  | [.battlefield], .all #[.hasSubtype (.literal s), .controlledBy .you] =>
    let s' ← takeSubtype s
    return { sc with pred := .all #[.hasSubtype (.literal s'), .controlledBy .you] }
  | _, _ => return sc

private def takeStaticCondition? : Option Condition → ArgM (Option Condition)
  | some (.cmp .ge (.aggregate .count .one (.inZones .yourGraveyard (.all #[.isCard, .hasType .creature]))) (.const n)) =>
    if n ≤ 1 then return some (.cmp .ge (.aggregate .count .one (.inZones .yourGraveyard (.all #[.isCard, .hasType .creature]))) (.const n))
    else do
      let k ← takeNat n.toNat
      return some (StaticAbility.condGyCreatureCardsAtLeast k)
  | some (.exists (.inZones .battlefield (.all #[.otherThan .this, .hasSubtype (.literal s), .controlledBy .you]))) =>
    return some (StaticAbility.condControlOtherSubtype (← takeSubtype s))
  | some (.exists (.inZones .battlefield (.all #[.hasSubtype (.literal s), .controlledBy .you]))) =>
    return some (StaticAbility.condControlSubtype (← takeSubtype s))
  | some (.exists (.inZones .battlefield (.all #[.hasType .planeswalker, .hasSubtype (.literal s), .controlledBy .you]))) =>
    return some (StaticAbility.condControlPlaneswalkerSubtype (← takeSubtype s))
  | some (.forAll .this (.stat .power .le (.const n))) =>
    return some (.forAll .this (.stat .power .le (.const (← takeInt n))))
  | other => return other

private def takeStaticKeywords (ks : Array KeywordAbility) : ArgM (Array KeywordAbility) := do
  ks.mapM fun
    | .ward (.mk #[.mana (.mk #[.generic w])] _) =>
      return .ward (CostSpec.ofGeneric (← takeNat w))
    | other => return other

private def takeStaticDynamicPT (p t : ValueExpr) : ArgM (ValueExpr × ValueExpr) := do
  match p, t with
  | .const pv, .const tv => return (.const (← takeInt pv), .const (← takeInt tv))
  | .binary .mul (.const 2) (.binary .divFloor (.playerMetric .graveyardSize .you) (.const 7)), .const 0 =>
    return (p, t)
  | pExpr, .const 0 =>
    match pExpr with
    | .binary .mul (.const k) inner =>
      return (StaticAbility.scaledValue (← takeInt k) inner, .const 0)
    | .aggregate .count .one (.inZones .battlefield (.all #[.otherThan .this, .hasType .artifact, .controlledBy .you])) =>
      return (StaticAbility.scaledValue (← takeInt 1) pExpr, .const 0)
    | .aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .attachedTo .this])) =>
      return (StaticAbility.scaledValue (← takeInt 1) pExpr, .const 0)
    | _ => return (p, t)
  | _, _ => return (p, t)

private partial def takeStaticContMod : ContinuousModification → ArgM ContinuousModification
  | .modifyPT p t => do
    let (p', t') ← takeStaticDynamicPT p t
    return .modifyPT p' t'
  | .grantKeywords ks => return .grantKeywords (← takeStaticKeywords ks)
  | .modifyTypes tm =>
    if tm.mode == .setAndKeepNoncreatureSubtypes && tm.subtypes.size == 1 then
      return .modifyTypes { tm with subtypes := #[← takeSubtype tm.subtypes[0]!] }
    else if tm.mode == .addDedup && tm.supertypes == #[.legendary] && !tm.subtypes.isEmpty then
      return .modifyTypes { tm with subtypes := ← takeSubtypes tm.subtypes }
    else return .modifyTypes tm
  | .copyActivatedFrom src =>
    match src.pred with
    | .all #[.isCard, .hasSubtype (.literal sub)] =>
      return .copyActivatedFrom { src with pred := .all #[.isCard, .hasSubtype (.literal (← takeSubtype sub))] }
    | _ => return .copyActivatedFrom src
  | .all ms => return .all (← ms.mapM takeStaticContMod)
  | other => return other

def takeStatic (ab : StaticAbility) : ArgM StaticAbility := do
  match ab with
  | .characteristicDefining (.setPT (some (.aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal sub), .controlledBy .you])))) none) =>
    return StaticAbility.powerEqualSubtypeYouControl (← takeSubtype sub)
  | .characteristicDefining _ => return ab
  | .continuous cond? sc mod =>
    -- Preserve text-order slot collection: condition before scope before mod, except trailing conditions
    let isTrailingCond :=
      sc == StaticAbility.scopeSelf &&
      match cond? with
      | some (.exists (.inZones .battlefield (.all #[.otherThan .this, .hasSubtype (.literal _), .controlledBy .you]))) => true
      | some (.exists (.inZones .battlefield (.all #[.hasType .planeswalker, .hasSubtype (.literal _), .controlledBy .you]))) => true
      | _ => false
    if isTrailingCond then
      let sc' ← takeStaticScope sc
      let mod' ← takeStaticContMod mod
      let cond?' ← takeStaticCondition? cond?
      return .continuous cond?' sc' mod'
    else
      let cond?' ← takeStaticCondition? cond?
      let sc' ← takeStaticScope sc
      let mod' ← takeStaticContMod mod
      return .continuous cond?' sc' mod'
  | .ruleModifying cond? rule =>
    match cond?, rule with
    | some (.forAll .this (.stat .power .le (.const n))), .combat (.cantBeBlocked .self) =>
      return StaticAbility.cantBeBlockedIfPowerAtMost (← takeInt n)
    | none, .combat (.cantBlock .self (some (.exists (.inZones .battlefield (.all #[subP, .controlledBy .you]))))) =>
      let subP' ← takeStaticAnySubPred subP
      return .ruleModifying none (.combat (.cantBlock .self (some (.exists (.inZones .battlefield (.all #[subP', .controlledBy .you]))))))
    | none, .combat (.cantAttackUnless .self (.cmp .ge (.aggregate .count .one (.inZones .battlefield (.all #[.otherThan .this, .hasSubtype (.literal sub), .controlledBy .you]))) (.const n))) =>
      let n' ← takeNat n.toNat
      let sub' ← takeSubtype sub
      return StaticAbility.cantAttackUnlessYouControlNOther n' sub'
    | none, .combat (.minBlockers .self n) =>
      return StaticAbility.cantBeBlockedExceptBy (← takeNat n)
    | none, .combat (.maxBlockers .self n) =>
      return StaticAbility.cantBeBlockedByMoreThan (← takeNat n)
    | none, .combat (.cantBeBlockedBy .self (.all #[.hasType .creature, .stat .power .le (.const n)])) =>
      return StaticAbility.cantBeBlockedByPowerAtMost (← takeInt n)
    | none, .combat (.cantBeBlockedBy .self (.all #[.hasType .creature, .stat .power .ge (.const n)])) =>
      return StaticAbility.cantBeBlockedByPowerAtLeast (← takeInt n)
    | some c, .combat (.attackTax ap df (.mk #[.mana (.mk #[.generic n])] _)) =>
      return .ruleModifying (some c) (.combat (.attackTax ap df (CostSpec.ofGeneric (← takeNat n))))
    | none, .player (.maxHandSize w (some n)) =>
      return .ruleModifying none (.player (.maxHandSize w (some (← takeNat n))))
    | cond?, .trigger (.extraTrigger sc extra) =>
      let sc' ← takeStaticScope sc
      return .ruleModifying cond? (.trigger (.extraTrigger sc' extra))
    | _, _ => return ab
  | .costModifier cond? tgt mod =>
    match tgt, mod with
    | .spells caster (.hasSubtype (.literal s)) none none az, .reduceGeneric (.const n) =>
      let s' ← takeSubtype s
      let n' ← takeNat n.toNat
      return .costModifier cond? (.spells caster (.hasSubtype (.literal s')) none none az) (.reduceGeneric (.const n'))
    | .spells caster (.hasType ty) none none az, .reduceGeneric (.const n) =>
      let ty' ← takeCardType ty
      let n' ← takeNat n.toNat
      return .costModifier cond? (.spells caster (.hasType ty') none none az) (.reduceGeneric (.const n'))
    | .spells caster (.hasSupertype sup) none none az, .reduceGeneric (.const n) =>
      let sup' ← takeSupertype sup
      let n' ← takeNat n.toNat
      return .costModifier cond? (.spells caster (.hasSupertype sup') none none az) (.reduceGeneric (.const n'))
    | .abilities act tag? sc tgt? nth?, .reduceGeneric (.const n) =>
      return .costModifier cond? (.abilities act tag? sc tgt? nth?) (.reduceGeneric (.const (← takeNat n.toNat)))
    | _, _ => return ab
  | .replacement _ _ => return ab
  | .enchantRestriction _ => return ab

mutual

partial def takeCostItem (item : CostItem) : ArgM CostItem := do
  match item with
  | .mana m => return .mana (← takeCost m)
  | .payLife (.const n) =>
    if n ≤ 0 then return item
    else return .payLife (.const (← takeNat n.toNat))
  | .sacrifice cnt (.filter (.all #[.otherThan .this, .hasSubtype (.literal sub)])) =>
    return .sacrifice cnt (.filter (.all #[.otherThan .this, .hasSubtype (.literal (← takeSubtype sub))]))
  | .behold sub => return .behold (← takeSubtype sub)
  | .or choices => return .or (← choices.mapM takeCostSpec)
  | other => return other

partial def takeCostSpec (c : CostSpec) : ArgM CostSpec := do
  let items ← c.items.mapM takeCostItem
  return { c with items }

end

def takeCostReduction (r : ActivationCostReduction) : ArgM ActivationCostReduction := do
  match r.amount, r.condition? with
  | .const n, some (.exists (.inZones .battlefield (.all #[.hasSupertype .legendary, .hasType .creature, .controlledBy .you]))) =>
    if n > 0 then
      let k ← takeNat n.toNat
      return ActivationCostReduction.ifControlLegendary k
    else return r
  | .aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .controlledBy .you])), none =>
    let k ← takeNat 1
    return ActivationCostReduction.perEquipment k
  | .binary .mul (.const n) (.aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .controlledBy .you]))), none =>
    if n > 0 then
      let k ← takeNat n.toNat
      return ActivationCostReduction.perEquipment k
    else return r
  | .const n, some (.all #[.exists (.target 0), .forAll (.target 0) (.all #[.hasType .creature, .stat .power .le (.const maxP)])]) =>
    if n > 0 then
      let k ← takeNat n.toNat
      let p ← takeInt maxP
      return ActivationCostReduction.ifTargetPowerAtMost k p
    else return r
  | _, _ => return r

def takeActivationCondition? : Option Condition → ArgM (Option Condition)
  | some (.exists (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you, .stat .toughness .ge (.const n)]))) => do
    if n > 0 then
      let k ← takeNat n.toNat
      return some (ActivatedAbility.condControlsCreatureToughnessAtLeast k)
    else return some (ActivatedAbility.condControlsCreatureToughnessAtLeast 0)
  | some (.cmp .ge (.aggregate .count .one (.inZones .yourGraveyard (.all #[.isCard, .hasType .creature]))) (.const n)) => do
    if n > 0 then
      let k ← takeNat n.toNat
      return some (ActivatedAbility.condGraveyardCreatureCardsAtLeast k)
    else return some (ActivatedAbility.condGraveyardCreatureCardsAtLeast 0)
  | other => return other

def takeActivated (ab : ActivatedAbility) : ArgM ActivatedAbility := do
  let cost ← takeCostSpec ab.cost
  let effect ← takeEffect ab.effect
  let costReductions ← ab.costReductions.mapM takeCostReduction
  let condition? ← takeActivationCondition? ab.condition?
  let tag? ←
    match ab.tag? with
    | some (.equip (some (.hasSubtype (.literal sub)))) =>
      match effect.targets.creatureYouControlSubtype? with
      | some s => pure (some (.equip (some (.hasSubtype (.literal s)))))
      | none => do
        let s ← takeSubtype sub
        pure (some (.equip (some (.hasSubtype (.literal s)))))
    | some (.cycling (some _)) =>
      match effect.body with
      | .player (.searchLibrary spec) =>
        match spec.filter with
        | .hasSubtype (.literal sub) => pure (some (.cycling (some sub.englishName)))
        | .hasSupertype sup => pure (some (.cycling (some sup.englishName)))
        | .hasType ty => pure (some (.cycling (some ty.englishName)))
        | .all #[.hasSupertype .basic, .hasType .land] => pure (some (.cycling (some "Basic land")))
        | _ => pure ab.tag?
      | _ => pure ab.tag?
    | other => pure other
  return { ab with cost, effect, costReductions, condition?, tag? }

def takeTriggered (ab : TriggeredAbility) : ArgM TriggeredAbility := do
  let pattern ← takeTriggerPattern ab.pattern
  let grouping ← takeTriggerGrouping ab.grouping
  let effect ← takeEffect ab.effect
  let interveningIf? ←
    match ab.interveningIf? with
    | some c => pure (some (← takeTriggerCond c))
    | none => pure none
  return { ab with pattern, grouping, interveningIf?, effect }

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

def slotTarget (vals : Array SlotVal) (i : Nat) : TargetSpec :=
  match vals[i]? with
  | some (.targets ts) => ts
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

/-- Longest target specification at the front of `toks` (already normalized),
parsed compositionally via `Parser.parseTargetSpecPrefix`. -/
def fromNounPrefix (toks : List String) : Option (TargetSpec × Nat) :=
  Parser.parseTargetSpecPrefix toks

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
  | .plural | .subPlural => pluralSubtype s
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
    | .plural => strWords (pluralSubtype s)
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

def kindHit (i : Nat) (ts : TargetSpec) (toks : List String) (fresh : Bool) : Option Hit :=
  let needle := tokenize (collapseWs (keepSignificant (replaceNumberWords (lowerAscii ts.noun))))
  if needle.isEmpty || !needle.isPrefixOf toks then none
  else some {
    width := needle.length
    used := if fresh then [i] else []
    pat := .kind i
    needle := String.intercalate " " needle
    repl := ts.noun
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
      | .targets ts =>
        hs := consider hs (kindHit i ts toks fresh)
      | .ctr _ => pure ()
    return hs.reverse

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
      | some (ts, n) =>
        match setSlot vals i (.targets ts) seen with
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
    | .nat i fmt =>
      let tag :=
        match fmt with
        | .digits => "d"
        | .cards => "c"
        | .counters => "k"
        | .brace => "b"
        | .english => "e"
        | .times => "x"
      s!"#{i}{tag}"
    | .int i fmt =>
      match fmt with
      | .signed => s!"#{i}+"
      | .digits => s!"#{i}i"
    | .str i fmt =>
      match fmt with
      | .word n => s!"$w{i}:{n}"
      | .plural => s!"$p{i}"
      | .cycling n => s!"$c{i}:{n}"
      | .non => s!"$n{i}"
      | .sub => s!"$s{i}"
      | .subPlural => s!"$sp{i}"
    | .ty i => s!"$t{i}"
    | .sup i => s!"$sup{i}"
    | .kind i => s!"$k{i}"
    | .pt i j signed => if signed then s!"+{i}/+{j}" else s!"#{i}/#{j}"
    | .counterPhrase i j => s!"#ctr{i}:{j}"
  String.intercalate "\n" (pats.map fun line => String.intercalate " " (line.map piece))

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

def refillEffect (e : Effect) (vals : Array SlotVal) : Effect :=
  runFill (takeEffect e) vals

def refillStatic (ab : StaticAbility) (vals : Array SlotVal) : StaticAbility :=
  runFill (takeStatic ab) vals

def refillActivated (ab : ActivatedAbility) (vals : Array SlotVal) : ActivatedAbility :=
  runFill (takeActivated ab) vals

def refillTriggered (ab : TriggeredAbility) (vals : Array SlotVal) : TriggeredAbility :=
  runFill (takeTriggered ab) vals

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
  match matchPats (patsOf (normalizeUnit "X" e.toNotation) args)
      (tokenize (normalizeUnit "X" query)) args with
  | some vals =>
    (refillEffect e vals).body ==
      .installEffect (.applyRule .untilEndOfTurn
        (.costMod (.spells .you (.hasType .planeswalker)) (.reduceGeneric (.const 3))))
  | none => false

/-- Refill `proto` from `query` and keep the Phase-8 `Instruction` body. -/
private def refilled (proto : Effect) (query : String) : Option Instruction :=
  let args := collectEffect proto
  match matchPats (patsOf (normalizeUnit "X" proto.toNotation) args)
      (tokenize (normalizeUnit "X" query)) args with
  | some vals => some (refillEffect proto vals).body
  | none => none

#guard (Effect.amassGoblins 1).toNotation == "amass Goblins 1"
#guard (Effect.riddlesInTheDark).toNotation ==
  "look at the top four cards of your library and separate them into a face-down pile and a face-up pile. An opponent chooses one of the piles. Put that pile into your hand and the other into your graveyard"
#guard (Effect.plusOneOnEachYouControl).toNotation ==
  "put a +1/+1 counter on each creature you control"
#guard (Effect.creatureYouControlDealsTwicePower).toNotation ==
  "target creature you control deals damage equal to twice its power to target creature an opponent controls"
#guard (Effect.drawThreeDiscardUnlessArtifact).toNotation ==
  "draw 3 cards. Then discard 2 cards unless you discard an artifact card"

#guard refilled (Effect.amassGoblins 1) "amass Zombies 4" ==
  some (Instruction.amassFixed 4 .zombie)

#guard refilled (Effect.riddlesInTheDark) "look at the top six cards of your library and separate them into a face-down pile and a face-up pile. An opponent chooses one of the piles. Put that pile into your hand and the other into your graveyard" ==
  some (.player (.inspectLibrary {
    source := .topCards .you (.const 6) false
    action := .splitIntoPiles .you .opponents 2 (.hand .controller) .graveyard
    rest := .leaveInPlace }))

#guard refilled (Effect.plusOneOnEachYouControl) "put 3 +1/+1 counters on each creature you control" ==
  some (Instruction.putPlusOne (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) 3)

#guard Effect.plusOneThenEachOtherIfFromGy.toNotation ==
  "put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, put a +1/+1 counter on each other creature you control"

#guard refilled Effect.plusOneThenEachOtherIfFromGy
    "Put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, put a +1/+1 counter on each other creature you control." ==
  some Effect.plusOneThenEachOtherIfFromGy.body

#guard refilled Effect.plusOneThenEachOtherIfFromGy
    "Put 2 +1/+1 counters on target creature you control. If this spell was cast from a graveyard, put 3 +1/+1 counters on each other creature you control." ==
  some (.seq #[
    Instruction.putPlusOne (.target 0) 2,
    Instruction.ifThen (.castPred (.castFrom .graveyard .this))
      (Instruction.putPlusOne
        (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you, .otherThan (.target 0)])) 3)])

#guard (Effect.plusOneUpToOneAndPlayerGainsLife 2).toNotation ==
  "put a +1/+1 counter on up to one target creature. Target player gains 2 life"

#guard refilled (Effect.plusOneUpToOneAndPlayerGainsLife 2)
    "Put a +1/+1 counter on up to one target creature. Target player gains 2 life." ==
  some (Effect.plusOneUpToOneAndPlayerGainsLife 2).body

#guard refilled (Effect.plusOneUpToOneAndPlayerGainsLife 2)
    "Put a stun counter on up to one target creature. Target player gains 4 life." ==
  some (Effect.plusOneUpToOneAndPlayerGainsLife 4 .stun).body

#guard refilled (Effect.plusOneUpToOneAndPlayerGainsLife 2)
    "Put two shield counters on up to one target creature. Target player gains 2 life." ==
  some (Effect.plusOneUpToOneAndPlayerGainsLife 2 .shield 2).body

#guard refilled (Effect.plusOneUpToOneAndPlayerGainsLife 2)
    "Put an indestructible counter on up to one target creature. Target player gains 2 life." ==
  some (Effect.plusOneUpToOneAndPlayerGainsLife 2 .indestructible).body

#guard refilled (Effect.plusOneUpToOneAndPlayerGainsLife 2)
    "Put a first strike counter on up to one target creature. Target player gains 1 life." ==
  some (Effect.plusOneUpToOneAndPlayerGainsLife 1 .firstStrike).body

#guard refilled (Effect.plusOneUpToOneAndPlayerGainsLife 2)
    "Put a -1/-1 counter on up to one target creature. Target player gains 2 life." ==
  some (Effect.plusOneUpToOneAndPlayerGainsLife 2 .minusOneMinusOne).body

#guard refilled (Effect.dealDamageToEachNonDragon 2) "deals 5 damage to each non-Elf creature" ==
  some (Instruction.dealDamageFixed
    (.objects (.inZones .battlefield (.all #[.hasType .creature, .not (.hasSubtype (.literal .elf))]))) 5)

#guard refilled (Effect.searchLegendaryCreatureToHand)
    "search your library for a basic land card, reveal it, put it into your hand, then shuffle" ==
  some (.player (.searchLibrary {
    zones := .libraryOf .you
    filter := .all #[.hasSupertype .basic, .hasType .land]
    count := .upTo (.const 1)
    dest := .hand .controller
    reveal := true
    shuffle := true }))

#guard refilled (Effect.creatureYouControlDealsTwicePower)
    "Target creature you control deals damage equal to 3 times its power to target creature an opponent controls." ==
  some (Effect.creatureYouControlDealsTwicePower 3).body

#guard refilled (Effect.drawThreeDiscardUnlessArtifact)
    "draw three cards. Then discard four cards unless you discard an enchantment card" ==
  some (.seq #[
    Instruction.drawFixed 3,
    .moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard {
      choice? := some {
        chooser := .controller
        count := .exact (.const 4)
        unlessMatching? := some (.hasType .enchantment) } }])

#guard refilled (Effect.becomeArtifactCreature44Flying)
    "until end of turn, target artifact or creature you control becomes an artifact creature with base power and toughness 2/3 and gains haste" ==
  some (.installEffect (.applyContinuous .untilEndOfTurn (.target 0)
    (.all #[
      .modifyTypes { types := #[.artifact, .creature] },
      .setBasePT (some (.const 2)) (some (.const 3)),
      .grantKeywords #[Keyword.haste] ])))

#guard refilled (Effect.mayDrawPerArtifactOppsDraw)
    "You may draw a card for each creature you control. If you do, each opponent draws a card" ==
  some (Instruction.may .you none
    (.seq #[
      Instruction.draw (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you]))),
      Instruction.drawFixed 1 .opponents ]))

#guard refilled (Effect.addRedPerOppArtifacts)
    "add {R} for each enchantment an opponent controls" ==
  some (Instruction.addMana {
    spec := .sequence #[(.colored .red,
      .aggregate .count .one (.inZones .battlefield (.all #[.hasType .enchantment, .controlledBy .opponent])))] })

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
  match matchPats (patsOf (normalizeUnit "X" e.toNotation) args)
      (tokenize (normalizeUnit "X" query)) args with
  | some vals =>
    (refillEffect e vals).body ==
      .installEffect (.applyRule .untilEndOfTurn
        (.costMod (.spells .you (.hasSupertype s)) (.reduceGeneric (.const 3))))
  | none => false

#guard
  let e := Effect.draw 2
  let args := collectEffect e
  match matchPats (patsOf (normalizeUnit "X" e.toNotation) args)
      (tokenize (normalizeUnit "X" "draw 7 cards")) args with
  | some vals => refillEffect e vals == Effect.draw 7
  | none => false

#guard
  let e := Effect.drawIfFromGy 1 2
  let args := collectEffect e
  match matchPats (patsOf (normalizeUnit "X" e.toNotation) args)
      (tokenize (normalizeUnit "X"
        "Draw a card. If this spell was cast from a graveyard, draw two cards instead.")) args with
  | some vals => refillEffect e vals == Effect.drawIfFromGy 1 2
  | none => false

#guard
  let e := Effect.drawIfFromGy 1 2
  let args := collectEffect e
  match matchPats (patsOf (normalizeUnit "X" e.toNotation) args)
      (tokenize (normalizeUnit "X"
        "Draw three cards. If this spell was cast from a graveyard, draw four cards instead.")) args with
  | some vals => refillEffect e vals == Effect.drawIfFromGy 3 4
  | none => false

#guard
  let e := Effect.amassGoblinsOrFromGy 1 3
  let args := collectEffect e
  match matchPats (patsOf (normalizeUnit "X" e.toNotation) args)
      (tokenize (normalizeUnit "X"
        "Amass Goblins 1. If this spell was cast from a graveyard, amass Goblins 3 instead.")) args with
  | some vals => refillEffect e vals == Effect.amassGoblinsOrFromGy 1 3
  | none => false

#guard
  let e := Effect.amassGoblinsOrFromGy 1 3
  let args := collectEffect e
  match matchPats (patsOf (normalizeUnit "X" e.toNotation) args)
      (tokenize (normalizeUnit "X"
        "Amass Zombies 2. If this spell was cast from a graveyard, amass Zombies 4 instead.")) args with
  | some vals =>
    (refillEffect e vals).body ==
      .ifCond (.castPred (.castFrom .graveyard .this))
        (Instruction.amassFixed 4 .zombie) (Instruction.amassFixed 2 .zombie)
  | none => false

#guard
  let e := Effect.searchLandTypeToHand "Mountain"
  let args := collectEffect e
  match matchPats (patsOf (normalizeUnit "X" e.toNotation) args)
      (tokenize (normalizeUnit "X" (Effect.searchLandTypeToHand "Forest").toNotation)) args with
  | some vals => refillEffect e vals == Effect.searchLandTypeToHand "Forest"
  | none => false

/-- `Effect.destroyCreature` refills to `target` from the target noun alone. -/
private def matchesDestroy (target : Effect) : Bool :=
  let proto := Effect.destroyCreature
  let args := collectEffect proto
  match matchPats (patsOf (normalizeUnit "X" proto.toNotation) args)
      (tokenize (normalizeUnit "X" target.toNotation)) args with
  | some vals => refillEffect proto vals == target
  | none => false

#guard collectEffect Effect.destroyCreature == #[.targets .creature]
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
  let line := normalizeUnit "X" Effect.destroyArtifactOrLandNonflyersCantBlock.toNotation
  matchPats (patsOf (normalizeUnit "X" proto.toNotation) args) (tokenize line) args == none

/-- `Effect.plusOneOnTarget 2` refills to the other counter counts and subtype lists. -/
private def matchesPlus (target : Effect) : Bool :=
  let proto := Effect.plusOneOnTarget 2
  let args := collectEffect proto
  match matchPats (patsOf (normalizeUnit "X" proto.toNotation) args)
      (tokenize (normalizeUnit "X" target.toNotation)) args with
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
  matchPats (patsOf (normalizeUnit "X" proto.toNotation) args) (tokenize line) args == none

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
  let noun := tokenize (lowerAscii (TargetSpec.noun .creatureYouControl))
  fromNounPrefix noun == some (.creatureYouControl, noun.length)
#guard
  let noun := tokenize (lowerAscii (TargetSpec.noun .legendaryCreatureYouControl))
  fromNounPrefix noun == some (.legendaryCreatureYouControl, noun.length)
#guard
  let noun := tokenize (lowerAscii (TargetSpec.noun .equipmentYouControl))
  fromNounPrefix noun == some (.equipmentYouControl, noun.length)

end Mtg.Engine.OracleArgs
