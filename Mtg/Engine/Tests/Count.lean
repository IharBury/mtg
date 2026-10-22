import Mtg.Engine.Fixture

/-!
# `ConditionSelector.atLeast`

The first `NumberSelector` is at least the second. `.count` is how many
objects an `ObjectSelector` names. `.fixed` is a printed number.
A legendary creature, lands, a planeswalker, other Forests, Bears,
a subtype, quest counters, another Hero, an equipped legend, a creature
or planeswalker target, creature cards in the graveyard, another subtype,
Equipment put from hand, a harnessed source, and an attacking source are
that count. Cards drawn this turn, loyalty removed, cards in the library,
and the source's power are the other printed comparisons. Any other pair
compares the same way.
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
  let (g, no) := holds afterDraw (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1))
  let g := addPermanent g hero caster caster
  let (g, one) := holds g (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1))
  let (g, two) := holds g (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 2))
  let g := addPermanent g bear caster caster
  let g := addPermanent g bear caster caster
  let (g, vsBears) :=
    holds g (.atLeast (.count .legendaryCreaturesYouControl) (.subtypeCount "Bear"))
  let g := addPermanent g hero caster caster
  let (_, twoHeroes) := holds g (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 2))
  !no && one && !two && !vsBears && twoHeroes &&
    !(g.log.any (· == "unused"))

/- Fewer than six lands is reported. Six lands hold without that report, and
zero is at least zero. -/
#guard
  let g := (List.range 5).foldl (fun g _ => addPermanent g forest caster caster) afterDraw
  let (g, five) := holds g (.atLeast (.count .landsYouControl) (.fixed 6))
  let fiveLog := logContains g "fewer than six lands"
  let g := addPermanent g forest caster caster
  let before := g.log.size
  let (g, six) := holds g (.atLeast (.count .landsYouControl) (.fixed 6))
  let (_, zero) := holds afterDraw (.atLeast (.count .landsYouControl) (.fixed 0))
  !five && fiveLog && six && g.log.size == before && zero

/- Controlling a planeswalker is reported. A higher count is not that report. -/
#guard
  let (g, noWalker) := holds afterDraw (.atLeast (.count .planeswalkersYouControl) (.fixed 1))
  let quiet := !logContains g "planeswalker"
  let g := addPermanent g walker caster caster
  let (g, one) := holds g (.atLeast (.count .planeswalkersYouControl) (.fixed 1))
  let reported := logContains g "control a planeswalker"
  let before := g.log.size
  let (g, two) := holds g (.atLeast (.count .planeswalkersYouControl) (.fixed 2))
  !noWalker && quiet && one && reported && !two && g.log.size == before

/- Forests other than the one that caused this. Five including that one is
four others. The cause's id is the last-known power. -/
#guard
  let g := (List.range 5).foldl (fun g _ => addPermanent g forest caster caster) afterDraw
  let cause := named g "Forest"
  let power := some (Int.ofNat cause.id.raw)
  let (g, four) := holds g (.atLeast (.count .forestsExceptCause) (.fixed 5)) (lastKnownPower := power)
  let reported := logContains g "fewer than five other Forests"
  let (g, enough) := holds g (.atLeast (.count .forestsExceptCause) (.fixed 4)) (lastKnownPower := power)
  let g := addPermanent g forest caster caster
  let (_, fiveOthers) :=
    holds g (.atLeast (.count .forestsExceptCause) (.subtypeCount "Forest")) (lastKnownPower := power)
  !four && reported && enough && !fiveOthers

/- Bears and any other subtype use the permanents you control. -/
#guard
  let g := addPermanent afterDraw bear caster caster
  let g := addPermanent g bear caster caster
  let (g, two) := holds g (.atLeast (.count (.youControl (.subtype "Bear"))) (.fixed 2))
  let (g, three) := holds g (.atLeast (.count (.youControl (.subtype "Bear"))) (.fixed 3))
  let g := addPermanent g isle caster caster
  let (_, isle) := holds g (.atLeast (.count (.youControl (.subtype "Bear"))) (.fixed 2))
  two && !three && isle

/- Quest counters are counted on the source. A missing source is reported. -/
#guard
  let g := addPermanent afterDraw questCard caster caster
  let src := named g "Count Quest"
  let (g, zero) := holds g (.atLeast (.count .questCounters) (.fixed 1)) (some src.id)
  let g := g.mapObjectStatus src (fun s => { s with quest := 6 })
  let (g, six) := holds g (.atLeast (.count .questCounters) (.fixed 6)) (some src.id)
  let (g, seven) := holds g (.atLeast (.count .questCounters) (.fixed 7)) (some src.id)
  let (g, missing) := holds g (.atLeast (.count .questCounters) (.fixed 0)) none
  !zero && six && !seven && !missing && logContains g "no longer in play"

/- Another Hero is a Hero other than the source. -/
#guard
  let g := addPermanent afterDraw hero caster caster
  let src := named g "Count Hero"
  let (g, only) :=
    holds g (.atLeast (.count (.othersOfSubtype "Hero")) (.fixed 1)) (some src.id)
  let g := addPermanent g hero caster caster
  let (_, another) :=
    holds g (.atLeast (.count (.othersOfSubtype "Hero")) (.fixed 1)) (some src.id)
  !only && another

/- The equipped creature must be a legendary creature you control. -/
#guard
  let g := addPermanent afterDraw bear caster caster
  let g := addPermanent g sword caster caster
  let host := named g "Count Bear"
  let eq := named g "Count Sword"
  let g := g.attachSourceTo eq host
  let (g, bearHost) := holds g (.atLeast (.count (.intersection [.equipped, .legendaryCreaturesYouControl])) (.fixed 1)) (some eq.id)
  let spirits := logContains g "Spirit tokens"
  let g := addPermanent g hero caster caster
  let legend := named g "Count Hero"
  let g := g.attachSourceTo (named g "Count Sword") legend
  let (g, legendHost) := holds g (.atLeast (.count (.intersection [.equipped, .legendaryCreaturesYouControl])) (.fixed 1)) (some eq.id)
  let (g, missing) := holds g (.atLeast (.count (.intersection [.equipped, .legendaryCreaturesYouControl])) (.fixed 1)) none
  !bearHost && spirits && legendHost && !missing &&
    logContains g "no longer in play"

/- Creature cards in the graveyard. A land in the graveyard does not count. -/
#guard
  let g := putInGraveyard afterDraw bear caster
  let g := putInGraveyard g isle caster
  let (g, one) := holds g (.atLeast (.count .creatureCardsInGraveyard) (.fixed 1))
  let (g, two) := holds g (.atLeast (.count .creatureCardsInGraveyard) (.fixed 2))
  let g := putInGraveyard g bear caster
  let (_, twoNow) := holds g (.atLeast (.count .creatureCardsInGraveyard) (.fixed 2))
  one && !two && twoNow

/- The source is attacking only while it is on the battlefield and attacking.
A harnessed source is reported when it is not. -/
#guard
  let g := addPermanent afterDraw bear caster caster
  let src := named g "Count Bear"
  let (g, idle) := holds g (.atLeast (.count (.intersection [.source, .attackingCreatures])) (.fixed 1)) (some src.id)
  let g := g.mapObjectStatus src (fun s => { s with attacking := true })
  let (g, attacking) := holds g (.atLeast (.count (.intersection [.source, .attackingCreatures])) (.fixed 1)) (some src.id)
  let (g, unharnessed) := holds g (.atLeast (.count .harnessedSource) (.fixed 1)) (some src.id)
  let g := g.mapObjectStatus (named g "Count Bear") (fun s => { s with harnessed := true })
  let (g, harnessed) := holds g (.atLeast (.count .harnessedSource) (.fixed 1)) (some src.id)
  let (_, gone) := holds g (.atLeast (.count (.intersection [.source, .attackingCreatures])) (.fixed 1)) none
  !idle && attacking && !unharnessed && logContains g "not harnessed" && harnessed && !gone

/- Equipment put from hand keeps the note. Another artifact clears it. -/
#guard
  let g := addPermanent afterDraw sword caster caster
  let g := addPermanent g bear caster caster
  let eq := named g "Count Sword"
  let host := named g "Count Bear"
  let g := { g with putArtifactThisWay := some (eq.id, host.id) }
  let (g, equip) := holds g (.atLeast (.count .putEquipment) (.fixed 1))
  let kept := g.putArtifactThisWay.isSome
  let g := addPermanent g isle caster caster
  let land := named g "Count Isle"
  let g := { g with putArtifactThisWay := some (land.id, host.id) }
  let (g, notEquip) := holds g (.atLeast (.count .putEquipment) (.fixed 1))
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
  let (g, heroTarget) := holds g (.atLeast (.count (.target (.anotherSubtype "Hero"))) (.fixed 1))
    (some src.id) #[Target.permanent other.id] (ab := ab)
  let (g, self) := holds g (.atLeast (.count (.target (.anotherSubtype "Hero"))) (.fixed 1))
    (some src.id) #[Target.permanent src.id] (ab := ab)
  let (g, bearTarget) := holds g (.atLeast (.count (.target (.anotherSubtype "Hero"))) (.fixed 1))
    (some src.id) #[Target.permanent bear.id] (ab := ab)
  let (g, creature) := holds g (.atLeast (.count (.target .creature)) (.fixed 1))
    (some src.id) #[Target.permanent bear.id] (ab := ab)
  let (g, walkerTarget) := holds g (.atLeast (.count (.target .planeswalker)) (.fixed 1))
    (some src.id) #[Target.permanent bear.id] (ab := ab)
  let (g, illegal) := holds g (.atLeast (.count (.target .creature)) (.fixed 1))
    (some src.id) #[] (ab := ab)
  heroTarget && !self && !bearTarget && creature && !walkerTarget && !illegal &&
    logContains g "no longer legal"

/- A restriction read on its own names that same target. `.target` is
`.any`. Any other restriction names nothing. -/
#guard
  let g := addPermanent afterDraw hero caster caster
  let g := addPermanent g bear caster caster
  let src := (g.battlefield.filter (·.name == "Count Hero"))[0]!
  let other := named g "Count Bear"
  let ab := TriggeredAbility.onEnterPlusOneOrTwoIfAnotherHero
  let (_, wrapped) := holds g (.atLeast (.count (.target .creature)) (.fixed 1))
    (some src.id) #[Target.permanent other.id] (ab := ab)
  let (_, bare) := holds g (.atLeast (.count .creature) (.fixed 1))
    (some src.id) #[Target.permanent other.id] (ab := ab)
  let (_, otherRestr) := holds g (.atLeast (.count (.target .source)) (.fixed 1))
    (some src.id) #[Target.permanent other.id] (ab := ab)
  let (_, bareHero) := holds g (.atLeast (.count (.anotherSubtype "Hero")) (.fixed 1))
    (some src.id) #[Target.permanent src.id] (ab := ab)
  wrapped && bare && !otherRestr && !bareHero &&
    (.target : TriggeredAbility.ObjectSelector) == .target .any &&
    .target .whileSource != (.target : TriggeredAbility.ObjectSelector)

/- A fixed number, cards drawn this turn, and loyalty removed as last-known
power. A number that cannot be read does not hold. -/
#guard
  let (_, one) := holds afterDraw (.atLeast (.fixed 1) (.fixed 2))
  let (_, same) := holds afterDraw (.atLeast (.fixed 2) (.fixed 2))
  let (_, negative) := holds afterDraw (.atLeast (.fixed (-1)) (.fixed (-3)))
  let (_, unread) := holds afterDraw (.atLeast .double (.fixed 0))
  let g := afterDraw
  let (g, drawnNone) := holds g (.atLeast .cardsDrawnThisTurn (.fixed 1))
  let g := (g.record (GameEvent.drew g.turnNumber caster ⟨11⟩ 1)).record
    (GameEvent.drew g.turnNumber caster ⟨12⟩ 2)
  let (g, drawnTwo) := holds g (.atLeast .cardsDrawnThisTurn (.fixed 2))
  let (g, drawnThree) := holds g (.atLeast .cardsDrawnThisTurn (.fixed 3))
  let (g, loyaltyMissing) := holds g (.atLeast .lastKnownPower (.fixed 2))
  let (g, loyaltyOne) :=
    holds g (.atLeast .lastKnownPower (.fixed 2)) (lastKnownPower := some 1)
  let (_, loyaltyTwo) :=
    holds g (.atLeast .lastKnownPower (.fixed 2)) (lastKnownPower := some 2)
  !one && same && negative && !unread && !drawnNone && drawnTwo && !drawnThree &&
    !loyaltyMissing && !loyaltyOne && loyaltyTwo

/- A library with a card, and an empty library. -/
#guard
  let filled := afterDraw.modifyPlayer caster (fun pl =>
    { pl with library := pl.library.push ⟨0⟩ })
  let (g, has) := holds filled (.atLeast .libraryCards (.fixed 1))
  let emptied := g.modifyPlayer caster (fun pl => { pl with library := #[] })
  let (g, empty) := holds emptied (.atLeast .libraryCards (.fixed 1))
  let (_, negated) := holds emptied (.not (.atLeast .libraryCards (.fixed 1)))
  has && !empty && negated && g.log.size == emptied.log.size

/- Source power uses the current power, then last-known power. Below 4 is
reported as Viv Vision's. Another threshold uses the generic report. -/
#guard
  let g := addPermanent afterDraw bear caster caster
  let src := named g "Count Bear"
  let (g, below4) := holds g (.atLeast .equalSourcePower (.fixed 4)) (some src.id)
  let viv := logContains g "Viv Vision's power is not 4 or greater"
  let (g, at2) := holds g (.atLeast .equalSourcePower (.fixed 2)) (some src.id)
  let (g, below3) := holds g (.atLeast .equalSourcePower (.fixed 3)) (some src.id)
  let other := logContains g "Its power is not 3 or greater"
  let (g, _) := g.move src.id (.graveyard caster) none
  let (g, leftHigh) := holds g (.atLeast .equalSourcePower (.fixed 4))
    (some src.id) (lastKnownPower := some 5)
  let (_, leftLow) := holds g (.atLeast .equalSourcePower (.fixed 4))
    (some src.id) (lastKnownPower := some 1)
  !below4 && viv && at2 && !below3 && other && leftHigh && !leftLow

/- `.intersection` names objects every selector names, in the first
selector's order. `.union` names objects any selector names, once, in
selector order. An empty list names nothing. A selector that does not
name permanents names nothing in an intersection and adds nothing in a
union. -/
#guard
  let g := addPermanent afterDraw bear caster caster
  let src := named g "Count Bear"
  let g := addPermanent g bear caster caster
  let g := addPermanent g hero caster caster
  let g := addPermanent g isle caster caster
  let g := addPermanent g sword caster caster
  let ctx : Game.TriggerRead := { controller := caster, sourceId := some src.id }
  let names (what : TriggeredAbility.ObjectSelector) : Option (Array String) :=
    (g.permanentsNamed ctx what).map (·.map (·.name))
  let heroes := .intersection [.creaturesYouControl, .youControl (.subtype "Hero")]
  let bearsAndHeroes := .union [.youControl (.subtype "Bear"), .youControl (.subtype "Hero")]
  let others := .intersection
    [.creaturesYouControl, .union [.othersOfSubtype "Bear", .othersOfSubtype "Hero"]]
  let attacking := .intersection [.source, .attackingCreatures]
  names heroes == some #["Count Hero"] &&
    names bearsAndHeroes == some #["Count Bear", "Count Bear", "Count Hero"] &&
    names others == some #["Count Bear", "Count Hero"] &&
    names (.intersection []) == some #[] &&
    names (.union []) == some #[] &&
    names (.intersection [.card, .creaturesYouControl]) == none &&
    names (.union [.card]) == none &&
    names (.union [.card, .artifact]) == some #["Count Sword"] &&
    g.countNamed ctx attacking == some 0 &&
    g.countNamed ctx (.union [.source, .attackingCreatures]) == some 1 &&
    (g.sacrificeCostCandidates ctx (.union [.another, .artifact])).map (·.name) ==
      #["Count Bear", "Count Hero", "Count Sword"] &&
    (g.sacrificeCostCandidates ctx (.intersection [.another, .artifact])).isEmpty

/- An attacking source is the intersection of the source and the attacking
creatures. Pumping creatures of a subtype leaves the other permanents. -/
#guard
  let g := addPermanent afterDraw bear caster caster
  let src := named g "Count Bear"
  let g := g.mapObjectStatus src (fun s => { s with attacking := true })
  let g := addPermanent g hero caster caster
  let g := g.mapObjectStatus (named g "Count Hero") (fun s => { s with attacking := true })
  let ctx : Game.TriggerRead := { controller := caster, sourceId := some src.id }
  let attacking := .intersection [.source, .attackingCreatures]
  let pumped := g.applyTriggeredAbility caster (.onEnterDraw 1) (some src.id)
    (resolutionOverride := some (.pump (.fixed 1) (.fixed 0)
      (.intersection [.creaturesYouControl, .youControl (.subtype "Hero")])))
  g.countNamed ctx attacking == some 1 &&
    g.countNamed ctx (.union [.source, .attackingCreatures]) == some 2 &&
    (named pumped "Count Hero").status.pumpPower == 1 &&
    (named pumped "Count Bear").status.pumpPower == 0

/- Discard candidates follow the same intersection and union. -/
#guard
  let cards := afterDraw.discardCostCandidates caster .card
  let nonlands := afterDraw.discardCostCandidates caster .nonland
  let both := afterDraw.discardCostCandidates caster (.intersection [.card, .nonland])
  let either := afterDraw.discardCostCandidates caster (.union [.card, .nonland])
  !cards.isEmpty &&
    both.map (·.id) == nonlands.map (·.id) &&
    either.map (·.id) == cards.map (·.id)

end Mtg.Engine.CountTests
