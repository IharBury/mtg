import Mtg.Engine.Game.Phasing

/-!
# Characteristic-defining P/T (CR 604.3)

Layer-7a characteristic-defining abilities: power/toughness equal to
lands you control, cards in hand, creatures you control, or subtype
counts, and the base P/T they define (CR 613.3a / 208.2a).
-/

namespace Mtg.Engine
namespace Game

/-- Mana value of other spells `p` has cast this turn. Copies that were not
cast are not recorded. -/
def otherCastManaValueThisTurn (g : Game) (p : PlayerId) : Nat :=
  (g.player p).castManaValuesThisTurn.foldl (· + ·) 0

/-- Lands `p` currently controls (CR 305.1). -/
def landsYouControl (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).filter (·.printed.isLand) |>.size

/-- Whether `o` currently has a “P/T equal to lands you control” ability.
This characteristic-defining ability functions in all zones (CR 208.2a / 604.3). -/
def hasLandsYouControlPT (_g : Game) (o : GameObject) : Bool :=
  o.staticAbilities.any StaticAbility.isLandsYouControlPT

/-- Power or toughness from a lands-you-control CDA (CR 208.2a / 604.3). -/
def landsYouControlPT (g : Game) (o : GameObject) : Int :=
  Int.ofNat (g.landsYouControl o.you)

/-- Characteristic power or toughness before pumps, counters, and attached
bonuses: an until-EOT layer-7b set on the battlefield, else lands you control
when that CDA applies (in all zones), else the printed value
(CR 208.2a / 604.3 / 613.3). -/
def characteristicBase (g : Game) (o : GameObject) (printed setBase : Option Int) : Int :=
  let fromCdaOrPrinted :=
    if g.hasLandsYouControlPT o then g.landsYouControlPT o else printed.getD 0
  if o.isOnBattlefield then setBase.getD fromCdaOrPrinted else fromCdaOrPrinted

/-- Whether `o` currently has a “power equal to cards in your hand” ability. -/
def hasCardsInHandPower (_g : Game) (o : GameObject) : Bool :=
  o.staticAbilities.any StaticAbility.isCardsInHandPower

/-- Characteristic power and toughness before pumps, counters, and attached
bonuses: an until-EOT layer-7b set on the battlefield, else lands you control
when that CDA applies (in all zones), else the printed values
(CR 208.2a / 604.3 / 613.3). -/
def hasCreaturesYouControlPower (_g : Game) (o : GameObject) : Bool :=
  o.staticAbilities.any StaticAbility.isCreaturesYouControlPower

/-- Subtype whose count defines this creature's power, if any. -/
def powerEqualSubtype? (o : GameObject) : Option String :=
  o.staticAbilities.foldl (fun acc ab =>
    match acc, ab with
    | none, .powerEqualSubtypeYouControl s => some s
    | acc, _ => acc) none

/-- True when `o` is Super-Adaptoid's characteristic-defining power (MSH 290). -/
def hasSuperAdaptoidPowerCda (o : GameObject) : Bool :=
  o.staticAbilities.any (fun
    | .powerEqualLegendaryCreaturesYouControl => true
    | _ => false)

def characteristicBasePT (g : Game) (o : GameObject) : Int × Int :=
  let power :=
    if g.hasCardsInHandPower o then
      -- Ms. Marvel (ruling 288): this set-P/T overwrites previous layer-7b sets.
      Int.ofNat (g.player o.you).hand.size
    else if let some subtype := powerEqualSubtype? o then
      let cda : Int :=
        Int.ofNat ((g.permanentsOf o.you).filter (fun p => p.hasSubtype subtype) |>.size)
      if o.isOnBattlefield then o.status.setBasePower.getD cda else cda
    else if hasSuperAdaptoidPowerCda o then
      let cda : Int :=
        Int.ofNat ((g.permanentsOf o.you).filter (fun p =>
          p.isCreature && p.isLegendary) |>.size)
      if o.isOnBattlefield then o.status.setBasePower.getD cda else cda
    else if g.hasCreaturesYouControlPower o then
      let fromTeam : Int :=
        Int.ofNat (g.countCreaturesControlledBy o.you)
      if o.isOnBattlefield then o.status.setBasePower.getD fromTeam else fromTeam
    else
      g.characteristicBase o o.printed.power o.status.setBasePower
  (power, g.characteristicBase o o.printed.toughness o.status.setBaseToughness)

/-- Characteristic power before pumps, counters, and attached bonuses. -/
def characteristicBasePower (g : Game) (o : GameObject) : Int :=
  (g.characteristicBasePT o).1

/-- Characteristic toughness before pumps, counters, and attached bonuses. -/
def characteristicBaseToughness (g : Game) (o : GameObject) : Int :=
  (g.characteristicBasePT o).2

end Game
end Mtg.Engine
