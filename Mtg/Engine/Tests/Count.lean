import Mtg.Engine.Fixture

/-!
# `ConditionSelector.countAtLeast`

At least `n` objects match an `ObjectSelector`. `.fixed` is the printed
count. A legendary creature, lands, a planeswalker, other Forests, Bears,
a subtype, quest counters, another Hero, an equipped legend, a creature
or planeswalker target, creature cards in the graveyard, another subtype,
Equipment put from hand, a harnessed source, and an attacking source are
that count. Any other pair compares the same way.
-/

namespace Mtg.Engine.CountTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

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

def isle : CardDef := land "Count Isle" "({T}: Add {C}.)" (tapAddMana := #[.colorless])

def holds (g : Game) (cond : TriggeredAbility.ConditionSelector)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (lastKnownPower : Option Int := none)
    (ab : TriggeredAbility := .onEnterDraw 1) : Game × Bool :=
  g.triggerIfHolds caster ab sourceId targets lastKnownPower cond

def named (g : Game) (name : String) : GameObject :=
  match g.battlefield.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def putInGraveyard (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.graveyard p) none {} (fun id pl =>
    { pl with graveyard := pl.graveyard.push id })

/- No legendary creature fails the printed check. One succeeds, and two
succeeds at a higher count. The threshold can be another count. -/
#guard
  let (g, no) := holds afterDraw (.countAtLeast .legendaryCreaturesYouControl (.fixed 1))
  let g := addPermanent g hero caster caster
  let (g, one) := holds g (.countAtLeast .legendaryCreaturesYouControl (.fixed 1))
  let (g, two) := holds g (.countAtLeast .legendaryCreaturesYouControl (.fixed 2))
  let g := addPermanent g bear caster caster
  let g := addPermanent g bear caster caster
  let (g, vsBears) :=
    holds g (.countAtLeast .legendaryCreaturesYouControl (.subtypeCount "Bear"))
  let g := addPermanent g hero caster caster
  let (_, twoHeroes) := holds g (.countAtLeast .legendaryCreaturesYouControl (.fixed 2))
  !no && one && !two && !vsBears && twoHeroes &&
    !(g.log.any (· == "unused"))

/- Fewer than six lands is reported. Six lands hold without that report, and
zero is at least zero. -/
#guard
  let g := (List.range 5).foldl (fun g _ => addPermanent g forest caster caster) afterDraw
  let (g, five) := holds g (.countAtLeast .landsYouControl (.fixed 6))
  let fiveLog := logContains g "fewer than six lands"
  let g := addPermanent g forest caster caster
  let before := g.log.size
  let (g, six) := holds g (.countAtLeast .landsYouControl (.fixed 6))
  let (_, zero) := holds afterDraw (.countAtLeast .landsYouControl (.fixed 0))
  !five && fiveLog && six && g.log.size == before && zero

/- Controlling a planeswalker is reported. A higher count is not that report. -/
#guard
  let (g, noWalker) := holds afterDraw (.countAtLeast .planeswalkersYouControl (.fixed 1))
  let quiet := !logContains g "planeswalker"
  let g := addPermanent g walker caster caster
  let (g, one) := holds g (.countAtLeast .planeswalkersYouControl (.fixed 1))
  let reported := logContains g "control a planeswalker"
  let before := g.log.size
  let (g, two) := holds g (.countAtLeast .planeswalkersYouControl (.fixed 2))
  !noWalker && quiet && one && reported && !two && g.log.size == before

/- Forests other than the one that caused this. Five including that one is
four others. The cause's id is the last-known power. -/
#guard
  let g := (List.range 5).foldl (fun g _ => addPermanent g forest caster caster) afterDraw
  let cause := named g "Forest"
  let power := some (Int.ofNat cause.id.raw)
  let (g, four) := holds g (.countAtLeast .forestsExceptCause (.fixed 5)) (lastKnownPower := power)
  let reported := logContains g "fewer than five other Forests"
  let (g, enough) := holds g (.countAtLeast .forestsExceptCause (.fixed 4)) (lastKnownPower := power)
  let g := addPermanent g forest caster caster
  let (_, fiveOthers) :=
    holds g (.countAtLeast .forestsExceptCause (.subtypeCount "Forest")) (lastKnownPower := power)
  !four && reported && enough && !fiveOthers

/- Bears and any other subtype use the permanents you control. -/
#guard
  let g := addPermanent afterDraw bear caster caster
  let g := addPermanent g bear caster caster
  let (g, two) := holds g (.countAtLeast (.youControl (.subtype "Bear")) (.fixed 2))
  let (g, three) := holds g (.countAtLeast (.youControl (.subtype "Bear")) (.fixed 3))
  let g := addPermanent g isle caster caster
  let (_, isle) := holds g (.countAtLeast (.youControl (.subtype "Bear")) (.fixed 2))
  two && !three && isle

/- Quest counters are counted on the source. A missing source is reported. -/
#guard
  let g := addPermanent afterDraw questCard caster caster
  let src := named g "Count Quest"
  let (g, zero) := holds g (.countAtLeast .questCounters (.fixed 1)) (some src.id)
  let g := g.mapObjectStatus src (fun s => { s with quest := 6 })
  let (g, six) := holds g (.countAtLeast .questCounters (.fixed 6)) (some src.id)
  let (g, seven) := holds g (.countAtLeast .questCounters (.fixed 7)) (some src.id)
  let (g, missing) := holds g (.countAtLeast .questCounters (.fixed 0)) none
  !zero && six && !seven && !missing && logContains g "no longer in play"

/- Another Hero is a Hero other than the source. -/
#guard
  let g := addPermanent afterDraw hero caster caster
  let src := named g "Count Hero"
  let (g, only) :=
    holds g (.countAtLeast (.othersOfSubtype "Hero") (.fixed 1)) (some src.id)
  let g := addPermanent g hero caster caster
  let (_, another) :=
    holds g (.countAtLeast (.othersOfSubtype "Hero") (.fixed 1)) (some src.id)
  !only && another

/- The equipped creature must be a legendary creature you control. -/
#guard
  let g := addPermanent afterDraw bear caster caster
  let g := addPermanent g sword caster caster
  let host := named g "Count Bear"
  let eq := named g "Count Sword"
  let g := g.attachSourceTo eq host
  let (g, bearHost) := holds g (.countAtLeast .equippedLegendary (.fixed 1)) (some eq.id)
  let spirits := logContains g "Spirit tokens"
  let g := addPermanent g hero caster caster
  let legend := named g "Count Hero"
  let g := g.attachSourceTo (named g "Count Sword") legend
  let (g, legendHost) := holds g (.countAtLeast .equippedLegendary (.fixed 1)) (some eq.id)
  let (g, missing) := holds g (.countAtLeast .equippedLegendary (.fixed 1)) none
  !bearHost && spirits && legendHost && !missing &&
    logContains g "no longer in play"

/- Creature cards in the graveyard. A land in the graveyard does not count. -/
#guard
  let g := putInGraveyard afterDraw bear caster
  let g := putInGraveyard g isle caster
  let (g, one) := holds g (.countAtLeast .creatureCardsInGraveyard (.fixed 1))
  let (g, two) := holds g (.countAtLeast .creatureCardsInGraveyard (.fixed 2))
  let g := putInGraveyard g bear caster
  let (_, twoNow) := holds g (.countAtLeast .creatureCardsInGraveyard (.fixed 2))
  one && !two && twoNow

/- The source is attacking only while it is on the battlefield and attacking.
A harnessed source is reported when it is not. -/
#guard
  let g := addPermanent afterDraw bear caster caster
  let src := named g "Count Bear"
  let (g, idle) := holds g (.countAtLeast .attackingSource (.fixed 1)) (some src.id)
  let g := g.mapObjectStatus src (fun s => { s with attacking := true })
  let (g, attacking) := holds g (.countAtLeast .attackingSource (.fixed 1)) (some src.id)
  let (g, unharnessed) := holds g (.countAtLeast .harnessedSource (.fixed 1)) (some src.id)
  let g := g.mapObjectStatus (named g "Count Bear") (fun s => { s with harnessed := true })
  let (g, harnessed) := holds g (.countAtLeast .harnessedSource (.fixed 1)) (some src.id)
  let (_, gone) := holds g (.countAtLeast .attackingSource (.fixed 1)) none
  !idle && attacking && !unharnessed && logContains g "not harnessed" && harnessed && !gone

/- Equipment put from hand keeps the note. Another artifact clears it. -/
#guard
  let g := addPermanent afterDraw sword caster caster
  let g := addPermanent g bear caster caster
  let eq := named g "Count Sword"
  let host := named g "Count Bear"
  let g := { g with putArtifactThisWay := some (eq.id, host.id) }
  let (g, equip) := holds g (.countAtLeast .putEquipment (.fixed 1))
  let kept := g.putArtifactThisWay.isSome
  let g := addPermanent g isle caster caster
  let land := named g "Count Isle"
  let g := { g with putArtifactThisWay := some (land.id, host.id) }
  let (g, notEquip) := holds g (.countAtLeast .putEquipment (.fixed 1))
  equip && kept && !notEquip && g.putArtifactThisWay.isNone

/- The announced creature is another Hero, or it is not. An illegal target
is reported. -/
#guard
  let g := addPermanent afterDraw hero caster caster
  let g := addPermanent g hero caster caster
  let g := addPermanent g bear caster caster
  let src := (g.battlefield.filter (·.name == "Count Hero"))[0]!
  let other := (g.battlefield.filter (·.name == "Count Hero"))[1]!
  let bear := named g "Count Bear"
  let ab := TriggeredAbility.onEnterPlusOneOrTwoIfAnotherHero
  let (g, heroTarget) := holds g (.countAtLeast (.targetAnotherSubtype "Hero") (.fixed 1))
    (some src.id) #[Target.permanent other.id] (ab := ab)
  let (g, self) := holds g (.countAtLeast (.targetAnotherSubtype "Hero") (.fixed 1))
    (some src.id) #[Target.permanent src.id] (ab := ab)
  let (g, bearTarget) := holds g (.countAtLeast (.targetAnotherSubtype "Hero") (.fixed 1))
    (some src.id) #[Target.permanent bear.id] (ab := ab)
  let (g, creature) := holds g (.countAtLeast .targetCreature (.fixed 1))
    (some src.id) #[Target.permanent bear.id] (ab := ab)
  let (g, walkerTarget) := holds g (.countAtLeast .targetPlaneswalker (.fixed 1))
    (some src.id) #[Target.permanent bear.id] (ab := ab)
  let (g, illegal) := holds g (.countAtLeast .targetCreature (.fixed 1))
    (some src.id) #[] (ab := ab)
  heroTarget && !self && !bearTarget && creature && !walkerTarget && !illegal &&
    logContains g "no longer legal"

end Mtg.Engine.CountTests
