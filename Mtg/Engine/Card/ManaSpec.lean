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
    | .commanderColorIdentity .you => "any one color in your commander's color identity"
    | .commanderColorIdentity who =>
      s!"any one color in {toOracleStr who { ctx with capitalize := false }}'s commander's color identity"
    | .colorsAmong objs =>
      s!"any color among {toOracleStr objs { ctx with plural := true, capitalize := false }}"
    | .typesLandsCouldProduce lands =>
      s!"any type that {toOracleStr lands { ctx with plural := true, capitalize := false }} could produce"

/-- Card-level declarative mana-production specification (CR 106.1 / 605). -/
inductive ManaSpec where
  /-- Fixed or quantity-scaled sequence of mana types (e.g. `{R}{R}`, or `{G}` for each Elf). -/
  | sequence (items : Array (ManaType × ValueExpr))
  /-- `amount` mana of any one type from `palette`. -/
  | oneOf (palette : ManaPoolPalette) (amount : ValueExpr := .const 1)
  /-- `amount` mana in any combination of types from `palette`. -/
  | combination (palette : ManaPoolPalette) (amount : ValueExpr := .const 1)
  /-- One mana of a color among `palette` (empty palette adds 0 mana, CR 106.1). -/
  | colorAmong (palette : ManaPoolPalette)
deriving Repr, Inhabited, BEq

namespace ManaSpec

/-- Lift an evaluated `ManaOutput` into a constant `ManaSpec`. -/
def ofOutput : ManaOutput → ManaSpec
  | .fixed m => .sequence (m.map (fun t => (t, .const 1)))
  | .oneOf ts n => .oneOf (.explicit ts) (.const (Int.ofNat n))
  | .combination ts n => .combination (.explicit ts) (.const (Int.ofNat n))
  | .colorAmong ts => .colorAmong (.explicit ts)

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
  | .colorAmong (.explicit ts) => some (.colorAmong ts)
  | .colorAmong .anyColor => some (.colorAmong anyColorMana)
  | _ => none

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
      | .colorAmong pal =>
        .colorAmong (HasTextChange.applyTextChanges tcs pal)

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
        s!"{toOracleStr amt { ctx with capitalize := false }} mana of any one color"
      | .oneOf pal (.const 1) =>
        s!"one mana of {toOracleStr pal { ctx with capitalize := false }}"
      | .oneOf pal amt =>
        s!"{toOracleStr amt { ctx with capitalize := false }} mana of {toOracleStr pal { ctx with capitalize := false }}"
      | .combination pal (.const n) =>
        s!"{englishNumber n.toNat} mana in any combination of {toOracleStr pal { ctx with capitalize := false }}"
      | .combination pal amt =>
        s!"{toOracleStr amt { ctx with capitalize := false }} mana in any combination of {toOracleStr pal { ctx with capitalize := false }}"
      | .colorAmong pal =>
        s!"one mana of {toOracleStr pal { ctx with capitalize := false }}"
    if ctx.capitalize then capitalizeAscii res else res

end Mtg.Engine
