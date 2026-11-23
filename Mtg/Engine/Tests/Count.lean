import Mtg.Engine.Fixture

/-!
# Unified `Condition.cmp`, `ValueExpr.count`, and `ObjectExpr` evaluation

`Condition.cmp .ge` compares two `ValueExpr`s. `ValueExpr.count` counts how many
objects an `ObjectExpr` names. `.const` is a printed number. Legendary creatures,
lands, planeswalkers, other Forests, Bears, subtypes, quest counters, another Hero,
an equipped legend, creature/planeswalker targets, graveyard creature cards,
harnessed/attacking sources, cards drawn this turn, library size, and power
comparisons all evaluate through `EvalExpr`.
-/

namespace Mtg.Engine.CountTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

def caster : PlayerId := ⟨0⟩

def bear : CardDef :=
  creature "Count Bear" ManaCost.empty #["Bear"] 2 2

def hero : CardDef :=
  creature "Count Hero" ManaCost.empty #["Hero"] 2 2 (supertypes := #[.legendary])

def walker : CardDef := {
  name := "Count Walker"
  types := #[.planeswalker]
  loyalty := some 4
}

def questCard : CardDef := {
  name := "Count Quest"
  types := #[.enchantment]
}

def sword : CardDef :=
  equipment "Count Sword" (ManaCost.ofGeneric 1) "" (ManaCost.ofGeneric 2)

def isle : CardDef :=
  land "Count Isle" "({T}: Add {C}.)"
    (activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 1)])])

def mkEnv (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (cause : Option GameObject := none) : EvalEnv :=
  { controller := caster
    sourceId
    targetSlots := targets.map fun t => #[t]
    triggerSubjectId := cause.map (·.id) }

def holds (g : Game) (cond : Condition)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (cause : Option GameObject := none) : Bool :=
  EvalExpr.evalCondition g (mkEnv sourceId targets cause) cond

def named (g : Game) (name : String) : GameObject :=
  match g.battlefield.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def putInGraveyard (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.graveyard p)

def legendaryCreaturesExpr : ObjectExpr :=
  .inZones .battlefield (.all #[.hasSupertype .legendary, .hasType .creature, .controlledBy .you])

def subtypeYouControlExpr (s : CardSubtype) : ObjectExpr :=
  .inZones .battlefield (.all #[.hasSubtype (.literal s), .controlledBy .you])

def othersOfSubtypeExpr (s : CardSubtype) : ObjectExpr :=
  .inZones .battlefield (.all #[.otherThan .this, .hasSubtype (.literal s), .controlledBy .you])

/- No legendary creature fails; one succeeds; two succeeds at threshold 2; comparing
against a subtype count works cleanly. -/
#guard
  let no := holds afterDraw (.cmp .ge (ValueExpr.count legendaryCreaturesExpr) (.const 1))
  let g := addPermanent afterDraw hero caster caster
  let one := holds g (.cmp .ge (ValueExpr.count legendaryCreaturesExpr) (.const 1))
  let two := holds g (.cmp .ge (ValueExpr.count legendaryCreaturesExpr) (.const 2))
  let g := addPermanent (addPermanent g bear caster caster) bear caster caster
  let vsBears :=
    holds g (.cmp .ge (ValueExpr.count legendaryCreaturesExpr) (ValueExpr.count (subtypeYouControlExpr .bear)))
  let g := addPermanent g hero caster caster
  let twoHeroes := holds g (.cmp .ge (ValueExpr.count legendaryCreaturesExpr) (.const 2))
  !no && one && !two && !vsBears && twoHeroes

/- Fewer than six lands fails, six lands holds, and zero is at least zero. -/
#guard
  let landsExpr : ObjectExpr := .inZones .battlefield (.all #[.hasType .land, .controlledBy .you])
  let g := (List.range 5).foldl (fun g _ => addPermanent g forest caster caster) afterDraw
  let five := holds g (.cmp .ge (ValueExpr.count landsExpr) (.const 6))
  let g := addPermanent g forest caster caster
  let six := holds g (.cmp .ge (ValueExpr.count landsExpr) (.const 6))
  let zero := holds afterDraw (.cmp .ge (ValueExpr.count landsExpr) (.const 0))
  !five && six && zero

/- Controlling a planeswalker vs two planeswalkers. -/
#guard
  let pwExpr : ObjectExpr := .inZones .battlefield (.all #[.hasType .planeswalker, .controlledBy .you])
  let noWalker := holds afterDraw (.cmp .ge (ValueExpr.count pwExpr) (.const 1))
  let g := addPermanent afterDraw walker caster caster
  let one := holds g (.cmp .ge (ValueExpr.count pwExpr) (.const 1))
  let two := holds g (.cmp .ge (ValueExpr.count pwExpr) (.const 2))
  !noWalker && one && !two

/- Forests other than the trigger subject. Five including that one is four others. -/
#guard
  let otherForests : ObjectExpr :=
    .inZones .battlefield (.all #[.otherThan .triggerSubject, .hasSubtype (.literal .forest), .controlledBy .you])
  let g := (List.range 5).foldl (fun g _ => addPermanent g forest caster caster) afterDraw
  let cause := named g "Forest"
  let four := holds g (.cmp .ge (ValueExpr.count otherForests) (.const 5)) (cause := some cause)
  let enough := holds g (.cmp .ge (ValueExpr.count otherForests) (.const 4)) (cause := some cause)
  let g := addPermanent g forest caster caster
  let fiveOthers :=
    holds g (.cmp .ge (ValueExpr.count otherForests) (ValueExpr.count (subtypeYouControlExpr .forest)))
      (cause := some cause)
  !four && enough && !fiveOthers

/- Bears and other subtypes use permanents you control. -/
#guard
  let g := addPermanent (addPermanent afterDraw bear caster caster) bear caster caster
  let two := holds g (.cmp .ge (ValueExpr.count (subtypeYouControlExpr .bear)) (.const 2))
  let three := holds g (.cmp .ge (ValueExpr.count (subtypeYouControlExpr .bear)) (.const 3))
  let g := addPermanent g isle caster caster
  let withIsle := holds g (.cmp .ge (ValueExpr.count (subtypeYouControlExpr .bear)) (.const 2))
  two && !three && withIsle

/- Quest counters are counted on the source. -/
#guard
  let g := addPermanent afterDraw questCard caster caster
  let src := named g "Count Quest"
  let zero := holds g (.cmp .ge (.counterCount (some .quest) .this) (.const 1)) (some src.id)
  let g := g.recordPutCounters src.id .quest 6
  let six := holds g (.cmp .ge (.counterCount (some .quest) .this) (.const 6)) (some src.id)
  let seven := holds g (.cmp .ge (.counterCount (some .quest) .this) (.const 7)) (some src.id)
  !zero && six && !seven

/- Another Hero is a Hero other than the source. -/
#guard
  let g := addPermanent afterDraw hero caster caster
  let src := named g "Count Hero"
  let only := holds g (.cmp .ge (ValueExpr.count (othersOfSubtypeExpr .hero)) (.const 1)) (some src.id)
  let g := addPermanent g hero caster caster
  let another := holds g (.cmp .ge (ValueExpr.count (othersOfSubtypeExpr .hero)) (.const 1)) (some src.id)
  !only && another

/- The equipped creature must be a legendary creature you control. -/
#guard
  let equippedLegend : ObjectExpr :=
    .filter .attachedHost (.all #[.hasSupertype .legendary, .hasType .creature, .controlledBy .you])
  let g := addPermanent (addPermanent afterDraw bear caster caster) sword caster caster
  let g := g.attachSourceTo (named g "Count Sword") (named g "Count Bear")
  let eqId := (named g "Count Sword").id
  let bearHost := holds g (.exists equippedLegend) (some eqId)
  let g := addPermanent g hero caster caster
  let g := g.attachSourceTo (named g "Count Sword") (named g "Count Hero")
  let legendHost := holds g (.exists equippedLegend) (some eqId)
  let missing := holds g (.exists equippedLegend) none
  !bearHost && legendHost && !missing

/- Creature cards in the graveyard. A land in the graveyard does not count. -/
#guard
  let gyCreatures : ObjectExpr := .inZones (.graveyardOf .you) (.hasType .creature)
  let g := putInGraveyard (putInGraveyard afterDraw bear caster) isle caster
  let one := holds g (.cmp .ge (ValueExpr.count gyCreatures) (.const 1))
  let two := holds g (.cmp .ge (ValueExpr.count gyCreatures) (.const 2))
  let g := putInGraveyard g bear caster
  let twoNow := holds g (.cmp .ge (ValueExpr.count gyCreatures) (.const 2))
  one && !two && twoNow

/- Attacking source and harnessed source checks. -/
#guard
  let attackingSource : Condition := .exists (.filter .this (.combatRole .attacking))
  let harnessedSource : Condition := .exists (.filter .this (.hasDesignation .harnessed))
  let g := addPermanent afterDraw bear caster caster
  let src := named g "Count Bear"
  let idle := holds g attackingSource (some src.id)
  let g := g.markAttacking src.id
  let attacking := holds g attackingSource (some src.id)
  let unharnessed := holds g harnessedSource (some src.id)
  let cBear := named g "Count Bear"
  let g := g.record (GameEvent.designation g.turnNumber (g.snapshot cBear) .harnessed true
    (cause := .gameRule .staticAbility))
  let harnessed := holds g harnessedSource (some src.id)
  let gone := holds g attackingSource none
  !idle && attacking && !unharnessed && harnessed && !gone

/- Target filtering: another Hero, creature, planeswalker. -/
#guard
  let g := addPermanent (addPermanent (addPermanent afterDraw hero caster caster) hero caster caster) bear caster caster
  let src := (g.battlefield.filter (·.name == "Count Hero"))[0]!
  let other := (g.battlefield.filter (·.name == "Count Hero"))[1]!
  let b := named g "Count Bear"
  let anotherHeroCond : Condition := .exists (.filter (.target 0) (.all #[.otherThan .this, .hasSubtype (.literal .hero)]))
  let creatureCond : Condition := .exists (.filter (.target 0) (.hasType .creature))
  let walkerCond : Condition := .exists (.filter (.target 0) (.hasType .planeswalker))
  let heroTarget := holds g anotherHeroCond (some src.id) #[Target.permanent other.id]
  let self := holds g anotherHeroCond (some src.id) #[Target.permanent src.id]
  let bearTarget := holds g anotherHeroCond (some src.id) #[Target.permanent b.id]
  let creature := holds g creatureCond (some src.id) #[Target.permanent b.id]
  let walkerTarget := holds g walkerCond (some src.id) #[Target.permanent b.id]
  let missing := holds g creatureCond (some src.id) #[]
  heroTarget && !self && !bearTarget && creature && !walkerTarget && !missing

/- Fixed numbers, cards drawn this turn, and library size. -/
#guard
  let one := holds afterDraw (.cmp .ge (.const 1) (.const 2))
  let same := holds afterDraw (.cmp .ge (.const 2) (.const 2))
  let negative := holds afterDraw (.cmp .ge (.const (-1)) (.const (-3)))
  let drawnNone := holds afterDraw (.cmp .ge (.playerMetric .cardsDrawnThisTurn .you) (.const 1))
  let g := (afterDraw.record (GameEvent.drew afterDraw.turnNumber caster ⟨11⟩ 1 (cause := .turnBased .drawStepDraw))).record
    (GameEvent.drew afterDraw.turnNumber caster ⟨12⟩ 2 (cause := .oneShotEffect none none (some caster)))
  let drawnTwo := holds g (.cmp .ge (.playerMetric .cardsDrawnThisTurn .you) (.const 2))
  let drawnThree := holds g (.cmp .ge (.playerMetric .cardsDrawnThisTurn .you) (.const 3))
  let filled := insertObject afterDraw hero caster (.library caster)
  let hasLib := holds filled (.cmp .ge (.playerMetric .librarySize .you) (.const 1))
  let emptied := emptyLibrary filled caster
  let emptyLib := holds emptied (.cmp .ge (.playerMetric .librarySize .you) (.const 1))
  let negated := holds emptied (.not (.cmp .ge (.playerMetric .librarySize .you) (.const 1)))
  !one && same && negative && !drawnNone && drawnTwo && !drawnThree &&
    hasLib && !emptyLib && negated

/- Source power comparison and pumping a filtered set of permanents. -/
#guard
  let g := addPermanent (addPermanent afterDraw bear caster caster) hero caster caster
  let src := named g "Count Bear"
  let below4 := holds g (.cmp .ge (.objectStat .power .this) (.const 4)) (some src.id)
  let at2 := holds g (.cmp .ge (.objectStat .power .this) (.const 2)) (some src.id)
  let below3 := holds g (.cmp .ge (.objectStat .power .this) (.const 3)) (some src.id)
  let ab := TriggeredAbility.mkTrigger .thisEnters {
    body := .installEffect (.applyContinuous .untilEndOfTurn
      (.inZones .battlefield (.all #[.hasType .creature, .hasSubtype (.literal .hero), .controlledBy .you]))
      (.modifyPT (.const 1) (.const 0)))
  }
  let pumped := g.applyTriggeredAbility caster ab (some src.id)
  !below4 && at2 && !below3 &&
    (pumped.pumpOf (named pumped "Count Hero")).1 == 1 &&
    (pumped.pumpOf (named pumped "Count Bear")).1 == 0

/- `ObjectPred.all` and `ObjectPred.any` compose cleanly in `EvalExpr.evalObjects`. -/
#guard
  let g := addPermanent (addPermanent (addPermanent (addPermanent (addPermanent afterDraw bear caster caster) bear caster caster) hero caster caster) isle caster caster) sword caster caster
  let src := named g "Count Bear"
  let env := mkEnv (some src.id)
  let names (e : ObjectExpr) : Array String :=
    (EvalExpr.evalObjects g env e).map fun | .live o => o.name | .lki eo => eo.name
  let heroes := names (.inZones .battlefield (.all #[.hasType .creature, .hasSubtype (.literal .hero), .controlledBy .you]))
  let bearsAndHeroes := names (.inZones .battlefield (.all #[.controlledBy .you, .any #[.hasSubtype (.literal .bear), .hasSubtype (.literal .hero)]]))
  let others := names (.inZones .battlefield (.all #[.otherThan .this, .hasType .creature, .controlledBy .you, .any #[.hasSubtype (.literal .bear), .hasSubtype (.literal .hero)]]))
  heroes == #["Count Hero"] &&
    bearsAndHeroes == #["Count Bear", "Count Bear", "Count Hero"] &&
    others == #["Count Bear", "Count Hero"]

end Mtg.Engine.CountTests
