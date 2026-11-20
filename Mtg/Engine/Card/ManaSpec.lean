import Mtg.Engine.Card.ManaTypes
import Mtg.Engine.Card.Expr

/-!
# Symbolic Mana Specifications (Layer 1 — CR 106, 605)

Card-level declarative mana-production specifications (`ManaPoolPalette`,
`ManaSpec`) parameterized over the Layer-1 expression algebra (`ValueExpr`,
`ObjectExpr`, `PlayerExpr`), anchored to the 25 September 2026 Comprehensive
Rules (CR 106.1, 106.6, 106.7, 605).

Layer-0 evaluated mana types (`ManaType`, `ManaOutput`, `ManaObjectPred`,
`ManaAbilityPred`, `SpellRiderSpec`, `ManaSpend`, `ManaSpendRestriction`) live
in `Mtg.Engine.Card.ManaTypes` below `Mtg.Engine.Mana` and are re-exported here.
-/

namespace Mtg.Engine

/-- Symbolic palette of mana types a mana ability can produce (CR 106.1 / 106.7). -/
inductive ManaPoolPalette where
  | explicit (types : Array ManaType)
  | anyColor
  | chosenColorOnSource
  | commanderColorIdentity (who : PlayerExpr := .you)
  | colorsAmong (objs : ObjectExpr)
  /-- Types of mana that lands matching `lands` could produce (CR 106.7, e.g.
  Exotic Orchard, Reflecting Pool). -/
  | typesLandsCouldProduce (lands : ObjectExpr)
deriving Repr, Inhabited, BEq

namespace ManaPoolPalette

/-- Whether this palette depends on CR 106.7 "could produce" land inspection
(skipped by `intrinsicLandMana` to break Reflecting Pool / Exotic Orchard cycles). -/
def usesLandsCouldProduce : ManaPoolPalette → Bool
  | .typesLandsCouldProduce _ => true
  | _ => false

end ManaPoolPalette

instance : HasTextChange ManaPoolPalette where
  applyTextChanges tcs p :=
    if tcs.isEmpty then p
    else
      match p with
      | .explicit ts => .explicit ts
      | .anyColor => .anyColor
      | .chosenColorOnSource => .chosenColorOnSource
      | .commanderColorIdentity who =>
        .commanderColorIdentity (HasTextChange.applyTextChanges tcs who)
      | .colorsAmong objs => .colorsAmong (HasTextChange.applyTextChanges tcs objs)
      | .typesLandsCouldProduce lands =>
        .typesLandsCouldProduce (HasTextChange.applyTextChanges tcs lands)

instance : ToOracle ManaPoolPalette where
  toOracle ctx
    | .explicit ts => manaSymbolsText ts " or "
    | .anyColor => "any color"
    | .chosenColorOnSource => "the chosen color"
    | .commanderColorIdentity .you => "any color in your commander's color identity"
    | .commanderColorIdentity who =>
      s!"any color in {toOracleStr who { ctx with capitalize := false }}'s commander's color identity"
    | .colorsAmong objs =>
      if objs == .legendaryCreaturesAndPlaneswalkersYouControl then
        "any color among legendary creatures and planeswalkers you control"
      else
        s!"any color among {toOracleStr objs { ctx with plural := true, capitalize := false }}"
    | .typesLandsCouldProduce lands =>
      if lands == .landsOpponentsControl then
        "any color that a land an opponent controls could produce"
      else if lands == .otherLandsYouControl || lands == .landsYouControl then
        "any type that a land you control could produce"
      else
        s!"any type that {toOracleStr lands { ctx with plural := true, capitalize := false }} could produce"

/-- Card-level declarative mana-production specification (CR 106.1 / 605). -/
inductive ManaSpec where
  /-- Fixed or quantity-scaled sequence of mana types (e.g. `{R}{R}`, or `{G}` for each Elf). -/
  | sequence (items : Array (ManaType × ValueExpr))
  /-- `amount` mana of any one type from `palette`. -/
  | oneOf (palette : ManaPoolPalette) (amount : ValueExpr := .const 1)
  /-- `amount` mana in any combination of types from `palette`. -/
  | combination (palette : ManaPoolPalette) (amount : ValueExpr := .const 1)
  /-- One mana of a type among `palette` (empty palette adds 0 mana, CR 106.1 / 106.7).
  When `includeColorless` is `false` ("any color", e.g. Exotic Orchard), `{C}` is excluded;
  when `true` ("any type", e.g. Reflecting Pool), `{C}` is included. -/
  | colorAmong (palette : ManaPoolPalette) (includeColorless : Bool := false)
deriving Repr, Inhabited, BEq

namespace ManaSpec

/-- Lift an evaluated `ManaOutput` into a constant `ManaSpec`. -/
def ofOutput : ManaOutput → ManaSpec
  | .fixed m => .sequence (m.map (fun t => (t, .const 1)))
  | .oneOf ts n => .oneOf (.explicit ts) (.const (Int.ofNat n))
  | .combination ts n => .combination (.explicit ts) (.const (Int.ofNat n))
  | .colorAmong ts incC => .colorAmong (.explicit ts) incC

/-- Single fixed mana type (`{C}`, `{G}`, etc.). -/
def fixedOne (t : ManaType) : ManaSpec :=
  .sequence #[(t, .const 1)]

/-- Fixed sequence of mana types (`{C}{C}`, `{W}{U}`, etc.). -/
def fixed (ts : Array ManaType) : ManaSpec :=
  .sequence (ts.map fun t => (t, .const 1))

/-- Project a constant `ManaSpec` (one requiring no game-state lookup) to a `ManaOutput`. -/
def toConstantOutput? : ManaSpec → Option ManaOutput
  | .sequence items =>
    let rec go (xs : List (ManaType × ValueExpr)) (acc : Array ManaType) : Option (Array ManaType) :=
      match xs with
      | [] => some acc
      | (t, v) :: rest =>
        match v.evalConst? 0 with
        | some n => go rest (acc ++ Array.replicate n.toNat t)
        | none => none
    (go items.toList #[]).map ManaOutput.fixed
  | .oneOf (.explicit ts) amt => (amt.evalConst? 0).map (fun n => .oneOf ts n.toNat)
  | .oneOf .anyColor amt => (amt.evalConst? 0).map (fun n => .oneOf anyColorMana n.toNat)
  | .combination (.explicit ts) amt => (amt.evalConst? 0).map (fun n => .combination ts n.toNat)
  | .combination .anyColor amt =>
    (amt.evalConst? 0).map (fun n => .combination anyColorMana n.toNat)
  | .colorAmong (.explicit ts) incC => some (.colorAmong ts incC)
  | .colorAmong .anyColor incC => some (.colorAmong anyColorMana incC)
  | _ => none

/-- Whether this `ManaSpec` queries CR 106.7 "could produce" on lands. -/
def usesLandsCouldProduce : ManaSpec → Bool
  | .oneOf pal _ | .combination pal _ | .colorAmong pal _ => pal.usesLandsCouldProduce
  | .sequence _ => false

/-- Best-effort static mana types this spec may produce (used by card-level
color-identity / summary queries). -/
def staticPossibleTypes : ManaSpec → Array ManaType
  | .sequence items => items.map Prod.fst
  | .oneOf (.explicit ts) _ | .combination (.explicit ts) _ | .colorAmong (.explicit ts) _ => ts
  | .oneOf .anyColor _ | .combination .anyColor _ | .colorAmong .anyColor _
  | .oneOf .chosenColorOnSource _ | .combination .chosenColorOnSource _
  | .colorAmong .chosenColorOnSource _
  | .oneOf (.commanderColorIdentity _) _ | .combination (.commanderColorIdentity _) _
  | .colorAmong (.commanderColorIdentity _) _
  | .oneOf (.colorsAmong _) _ | .combination (.colorsAmong _) _
  | .colorAmong (.colorsAmong _) _ => anyColorMana
  | .oneOf (.typesLandsCouldProduce _) _ | .combination (.typesLandsCouldProduce _) _
  | .colorAmong (.typesLandsCouldProduce _) _ => #[]

end ManaSpec

instance : HasTextChange ManaSpec where
  applyTextChanges tcs s :=
    if tcs.isEmpty then s
    else
      match s with
      | .sequence items =>
        .sequence (items.map fun (t, amt) => (t, HasTextChange.applyTextChanges tcs amt))
      | .oneOf pal amt =>
        .oneOf (HasTextChange.applyTextChanges tcs pal) (HasTextChange.applyTextChanges tcs amt)
      | .combination pal amt =>
        .combination (HasTextChange.applyTextChanges tcs pal) (HasTextChange.applyTextChanges tcs amt)
      | .colorAmong pal incC =>
        .colorAmong (HasTextChange.applyTextChanges tcs pal) incC

private def andOrJoin (xs : List String) : String :=
  match xs with
  | [] => ""
  | [a] => a
  | [a, b] => s!"{a} and/or {b}"
  | _ =>
    let init := xs.dropLast
    let last := xs.getLastD ""
    s!"{String.intercalate ", " init}, and/or {last}"

instance : ToOracle ManaSpec where
  toOracle ctx s :=
    let res :=
      match s with
      | .sequence items =>
        let parts := items.toList.map fun (t, amt) =>
          match amt with
          | .const 1 => s!"\{{t.letter}}"
          | .const n =>
            if n ≤ 0 then "" else String.join (List.replicate n.toNat s!"\{{t.letter}}")
          | .aggregate .count _ objs =>
            s!"\{{t.letter}} for each {toOracleStr objs { ctx with plural := false, capitalize := false }}"
          | other =>
            s!"{toOracleStr other { ctx with capitalize := false }} \{{t.letter}}"
        String.intercalate "" (parts.filter (!·.isEmpty))
      | .oneOf (.explicit ts) (.const 1) => manaSymbolsText ts " or "
      | .oneOf .anyColor (.const 1) => "one mana of any color"
      | .oneOf .anyColor (.const n) => s!"{englishNumber n.toNat} mana of any one color"
      | .oneOf .anyColor amt =>
        s!"X mana of any one color, where X is {toOracleStr amt { ctx with capitalize := false }}"
      | .oneOf .chosenColorOnSource (.const 1) => "one mana of the chosen color"
      | .oneOf pal (.const 1) =>
        s!"one mana of {toOracleStr pal { ctx with capitalize := false }}"
      | .oneOf pal (.const n) =>
        s!"{englishNumber n.toNat} mana of {toOracleStr pal { ctx with capitalize := false }}"
      | .oneOf pal amt =>
        s!"X mana of {toOracleStr pal { ctx with capitalize := false }}, where X is {toOracleStr amt { ctx with capitalize := false }}"
      | .combination .anyColor (.const n) =>
        s!"{englishNumber n.toNat} mana in any combination of colors"
      | .combination (.explicit ts) (.const n) =>
        s!"{englishNumber n.toNat} mana in any combination of {andOrJoin (ts.toList.map fun t => s!"\{{t.letter}}")}"
      | .combination pal (.const n) =>
        s!"{englishNumber n.toNat} mana in any combination of {toOracleStr pal { ctx with capitalize := false }}"
      | .combination pal amt =>
        s!"{toOracleStr amt { ctx with capitalize := false }} mana in any combination of {toOracleStr pal { ctx with capitalize := false }}"
      | .colorAmong (.typesLandsCouldProduce lands) false =>
        if lands == .landsOpponentsControl then
          "one mana of any color that a land an opponent controls could produce"
        else
          s!"one mana of any color that {toOracleStr lands { ctx with plural := true, capitalize := false }} could produce"
      | .colorAmong (.typesLandsCouldProduce lands) true =>
        if lands == .otherLandsYouControl || lands == .landsYouControl then
          "one mana of any type that a land you control could produce"
        else
          s!"one mana of any type that {toOracleStr lands { ctx with plural := true, capitalize := false }} could produce"
      | .colorAmong pal _ =>
        s!"one mana of {toOracleStr pal { ctx with capitalize := false }}"
    if ctx.capitalize then capitalizeAscii res else res

/-- Complete declarative mana-production specification carried by an
`ActivatedAbility` (CR 106.1 / 106.6 / 605.1a). Combines the symbolic
`ManaSpec` with any spending restriction, spell riders, and resolution
self-damage (e.g. painlands, talismans). -/
structure ManaProductionSpec where
  spec : ManaSpec
  restriction : Option ManaSpendRestriction := none
  riders : Array SpellRiderSpec := #[]
  /-- Damage the source deals to its controller as this mana ability resolves
  (CR 605.3b, e.g. painlands / talismans). -/
  damageYou : Nat := 0
  /-- Render as `"Choose a color. Add one mana of that color for each ..."` when true. -/
  chooseColorPrefix : Bool := false
  /-- Render a 2-color `.combination (.explicit #[a, b]) (.const 2)` as
  `"Add {A}{A}, {A}{B}, or {B}{B}."` (Shadowmoor/Eventide filter lands). -/
  filterPairFormat : Bool := false
deriving Repr, Inhabited, BEq

namespace ManaProductionSpec

/-- All spell riders attached to this mana production (combining `riders` with
any riders embedded on `restriction`). -/
def allRiders (m : ManaProductionSpec) : Array SpellRiderSpec :=
  let fromRestr := match m.restriction with | some r => r.riders | none => #[]
  m.riders.foldl (fun acc r => if acc.contains r then acc else acc.push r) fromRestr

/-- Render the effect body of a mana ability (everything after `":"`), e.g.
`"Add {G}."`, `"Add {U} or {B}. This land deals 1 damage to you."`, or
`"Add one mana of any color. Spend this mana only to cast an instant or sorcery spell."`. -/
def toOracleSentence (m : ManaProductionSpec) (ctx : PrintCtx := {}) : String :=
  let addSentence :=
    if m.chooseColorPrefix then
      match m.spec with
      | .oneOf .anyColor (.aggregate .countDistinct (.stat .power) objs) =>
        s!"Choose a color. Add one mana of that color for each different power among {toOracleStr objs { ctx with plural := true, capitalize := false }}."
      | .oneOf .anyColor (.aggregate .count _ objs) =>
        s!"Choose a color. Add one mana of that color for each {toOracleStr objs { ctx with plural := false, capitalize := false }}."
      | .oneOf .anyColor amt =>
        let rawAmt := toOracleStr amt { ctx with capitalize := false }
        let forEachRest :=
          if rawAmt.startsWith "the number of " then (rawAmt.drop 14).copy
          else rawAmt
        s!"Choose a color. Add one mana of that color for each {forEachRest}."
      | other => s!"Choose a color. Add {toOracleStr other { ctx with capitalize := false }}."
    else if m.filterPairFormat then
      match m.spec with
      | .combination (.explicit ts) (.const 2) =>
        if h : ts.size = 2 then
          let a := ts[0].letter
          let b := ts[1].letter
          s!"Add \{{a}}\{{a}}, \{{a}}\{{b}}, or \{{b}}\{{b}}."
        else
          s!"Add {toOracleStr m.spec { ctx with capitalize := false }}."
      | _ => s!"Add {toOracleStr m.spec { ctx with capitalize := false }}."
    else
      s!"Add {toOracleStr m.spec { ctx with capitalize := false }}."
  let dmgSentence :=
    if m.damageYou > 0 then [s!"{capitalizeAscii ctx.selfRef} deals {m.damageYou} damage to you."]
    else []
  let restrSentence :=
    match m.restriction with
    | some r => [r.toOracleSentence]
    | none => []
  let restrRiders := match m.restriction with | some r => r.riders | none => #[]
  let extraRiderSentences :=
    (m.riders.filter fun r => !restrRiders.contains r).toList.map SpellRiderSpec.toStandaloneSentence
  String.intercalate " " ([addSentence] ++ dmgSentence ++ restrSentence ++ extraRiderSentences)

end ManaProductionSpec

instance : HasTextChange ManaProductionSpec where
  applyTextChanges tcs m :=
    if tcs.isEmpty then m
    else
      { m with
        spec := HasTextChange.applyTextChanges tcs m.spec
        restriction := m.restriction.map (HasTextChange.applyTextChanges tcs) }

instance : ToOracle ManaProductionSpec where
  toOracle ctx m := m.toOracleSentence ctx

end Mtg.Engine
