import Mtg.Engine.FraOracleTests3
import Mtg.Engine.FraOracleTests7

/-!
# Reality Fracture cards: spells

Game-state checks for every Reality Fracture instant and sorcery (and
prepare spell) whose rules text the parser now models. Each card is parsed
from its printed text, cast, and resolved.
-/

namespace Mtg.Engine.FraCardTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests
open Mtg.Engine.FraRulingTests

def me : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

/-- Add `n` mana of every color to `p`'s pool. -/
def everyColor (g : Game) (p : PlayerId := me) (n : Nat := 4) : Game :=
  [Color.white, .blue, .black, .red, .green].foldl (fun g c => withMana g p c n) g

/-- Put `card` into `p`'s hand and cast it: `steps` announce modes, costs, and
targets in order; then pay. -/
def castFra (g : Game) (card : CardDef) (steps : List Action := []) (p : PlayerId := me) :
    Game :=
  let g := everyColor (addToHand g card p) p
  let g := mustApply g p (.cast (handCardNamed g p card.name).id)
  let g := steps.foldl (fun g a => mustApply g p a) g
  mustApply g p .pay

def resolved (g : Game) : Game := resolveStack g 40

def perm (g : Game) (name : String) : Target := .permanent (namedPermanent g name).id

def tgt (g : Game) (name : String) : Action := .target (perm g name)

def gyTarget (g : Game) (p : PlayerId) (name : String) : Action :=
  .target (.card (graveyardCard g p name).id)

def handSize (g : Game) (p : PlayerId) : Nat := (g.player p).hand.size

def life (g : Game) (p : PlayerId) : Int := (g.player p).life

def inGraveyard (g : Game) (p : PlayerId) (name : String) : Bool :=
  (g.player p).graveyard.any (fun id => (g.object! id).name == name)

def inExile (g : Game) (name : String) : Bool :=
  g.objects.any (fun o => o.zone == .exile && o.name == name)

def inHand (g : Game) (p : PlayerId) (name : String) : Bool :=
  (g.handObjects p).any (·.name == name)

def counters (g : Game) (name : String) : Nat :=
  (namedPermanent g name).status.plusOnePlusOne

def creaturesNamed (g : Game) (name : String) : Nat :=
  (g.battlefield.filter (·.name == name)).size

/-- True when casting `card` with `steps` is rejected at some step. -/
def castRejected (g : Game) (card : CardDef) (steps : List Action) (p : PlayerId := me) : Bool :=
  let g := everyColor (addToHand g card p) p
  let run := (g.apply p (.cast (handCardNamed g p card.name).id)).bind fun g =>
    steps.foldlM (fun g a => g.apply p a) g
  match run with
  | .error _ => true
  | .ok _ => false

def withBears : Game := addPermanent afterDraw grizzlyBears opp opp
def withGiant : Game := addPermanent afterDraw hillGiant opp opp

/- Every FRA spell's rules text is modeled: no printed text is left over. -/
#guard [generousRevival, hexhavenBattalion, kindredJudgment, loyalTutor,
    predictivePreparations, prophesiedEnd, refuteDestiny, returnToTheLightRealms,
    surgicalPrecision, yourFateEndsHere, countersculpt, cruelCalculations,
    icyReception, preciseRedaction, sphinxsApproach, unsummon, castAwayDoubt,
    extendedAbsence, extrapolateTheImpossible, overwriteTheMultiverse, rewriteRegrets,
    riseOfTheDeathbringer, silenceTheEcho, solveForDisappointment, terminalCriticism,
    vraskasFinalMercy, artifistAcumen, awakenTheInferno, essenceBurn,
    fulminousForte, wrathOfTheBloodmane, flourishingGrapple, restoreWithEmpathy,
    somethingWorthSaving, tethermagesAdvantage, chargeTheSanctum, clashOfElements,
    entrustTheSpark, fateholdCharm, konstrariCharm, recursiveRecruitment,
    stingerquillCharm, stingingVitriol, tamsResistance, theorixCharm, twinnedVision,
    twistedFates, vigorbloomCharm, vindictiveTriumph].all (!keepsPrintedText ·)

/-! ## White -/

/- Generous Revival returns a creature card with mana value 3 or less with an
additional +1/+1 counter; Hill Giant (mana value 4) isn't a legal target. -/
#guard
  let g := addToGraveyard afterDraw grizzlyBears me
  let g := resolved (castFra g generousRevival [gyTarget g me "Grizzly Bears"])
  counters g "Grizzly Bears" == 1
#guard
  let g := addToGraveyard afterDraw hillGiant me
  castRejected g generousRevival [gyTarget g me "Hill Giant"]
#guard generousRevival.flashback.isSome

/- Hexhaven Battalion creates three Cadets and empowers Jace 2. -/
#guard
  let g := resolved (castFra afterDraw hexhavenBattalion)
  creaturesNamed g "Cadet" == 3 && (jaceTokenOf g).status.loyaltyCounters == 2

/- Kindred Judgment: the caster chooses Bear, the type of their creatures, so
only the opponent's Hill Giant and Gray Ogre are destroyed. -/
#guard
  let g := addPermanent withGiant grayOgre opp opp
  let g := addPermanent g grizzlyBears me me
  let g := resolved (castFra g kindredJudgment)
  onBattlefield g "Grizzly Bears" && !onBattlefield g "Hill Giant" && !onBattlefield g "Gray Ogre"

/- Loyal Tutor puts a planeswalker card on top of the library. -/
#guard
  let g := addToLibraryTop afterDraw jaceRealitySculptor me
  let g := addToLibraryTop g grizzlyBears me
  let g := resolved (castFra g loyalTutor)
  ((g.player me).library.back?.map (fun id => (g.object! id).name)) == some "Jace, Reality Sculptor"

/- Predictive Preparations puts a counter on each of two target creatures. -/
#guard
  let g := addPermanent withBears grizzlyBears me me
  let mine := (g.permanentsOf me).find? (·.name == "Grizzly Bears") |>.get!
  let theirs := (g.permanentsOf opp).find? (·.name == "Grizzly Bears") |>.get!
  let g := resolved (castFra g predictivePreparations
    [.targets #[.permanent mine.id, .permanent theirs.id]])
  (g.object! mine.id).status.plusOnePlusOne == 1 && (g.object! theirs.id).status.plusOnePlusOne == 1

/- Prophesied End: a creature that wasn't attacking is destroyed and its
controller draws a card. -/
#guard
  let before := handSize withBears opp
  let g := resolved (castFra withBears prophesiedEnd [tgt withBears "Grizzly Bears"])
  !onBattlefield g "Grizzly Bears" && handSize g opp == before + 1

/- Refute Destiny exiles a green or blue creature or planeswalker, then
surveils 1. A red creature isn't a legal target. -/
#guard
  let g := castFra withBears refuteDestiny [tgt withBears "Grizzly Bears"]
  let g := passBoth g
  inExile g "Grizzly Bears" && g.pending == .surveil me 1
#guard castRejected withGiant refuteDestiny [tgt withGiant "Hill Giant"]

/- Return to the Light Realms returns nonland permanent cards only. -/
#guard
  let g := addToGraveyard afterDraw grizzlyBears me
  let g := addToGraveyard g mountain me
  let g := addToGraveyard g hillGiant me
  let g := resolved (castFra g returnToTheLightRealms)
  onBattlefield g "Grizzly Bears" && onBattlefield g "Hill Giant" && inGraveyard g me "Mountain"

/- Surgical Precision: destroy a creature with toughness 4 or greater and gain
1 life, or draw a card and gain 2 life. -/
#guard
  let g := addPermanent afterDraw crawWurm opp opp
  let g := resolved (castFra g surgicalPrecision [.chooseMode 0, tgt g "Craw Wurm"])
  !onBattlefield g "Craw Wurm" && life g me == 21
#guard castRejected withBears surgicalPrecision [.chooseMode 0, tgt withBears "Grizzly Bears"]
#guard
  let g := resolved (castFra afterDraw surgicalPrecision [.chooseMode 1])
  life g me == 22 && handSize g me == handSize afterDraw me + 1

/- Your Fate Ends Here destroys a creature with mana value 3 or greater, then
surveils 1. -/
#guard
  let g := passBoth (castFra withGiant yourFateEndsHere [tgt withGiant "Hill Giant"])
  !onBattlefield g "Hill Giant" && g.pending == .surveil me 1
#guard castRejected withBears yourFateEndsHere [tgt withBears "Grizzly Bears"]

/-! ## Blue -/

/-- Cast Shock at the opponent and keep priority (it stays on the stack). -/
def shockOnStack (g : Game) : Game :=
  castFra g shock [.target (.player opp)]

def stackSpell (g : Game) (name : String) : Target :=
  match g.stack.find? (fun e => (g.object! e.objectId).name == name) with
  | some e => .card e.objectId
  | none => panic! s!"expected {name} on the stack"

/- Countersculpt counters target spell and empowers Jace 1. -/
#guard
  let g := shockOnStack afterDraw
  let g := castFra g countersculpt [.chooseAdditionalCost true, .target (stackSpell g "Shock")]
  let g := resolved g
  life g opp == 20 && inGraveyard g me "Shock" && (jaceTokenOf g).status.loyaltyCounters == 1

/- Cruel Calculations draws a card for each card milled from the target
player's library this turn. -/
#guard
  let g := afterDraw.mill opp 3
  let before := handSize g me
  let g := resolved (castFra g cruelCalculations [.target (.player opp)])
  handSize g me == before + 3

/- Icy Reception counters a creature spell unless its controller pays {3}, or
gives a creature minus five power. -/
#guard
  let g := castFra afterDraw grizzlyBears
  let g := castFra g icyReception [.chooseMode 0, .target (stackSpell g "Grizzly Bears")]
  let g := passBoth g
  match g.pending with
  | .payOrLetCounter p 3 _ =>
    let g := mustApply g p .decline
    inGraveyard (resolved g) me "Grizzly Bears"
  | _ => false
#guard
  let g := resolved (castFra withGiant icyReception [.chooseMode 1, tgt withGiant "Hill Giant"])
  g.power (namedPermanent g "Hill Giant") == -2

/- Precise Redaction counters only a white or black spell. -/
#guard
  let g := castFra afterDraw castAwayDoubt
  let g := resolved (castFra g preciseRedaction [.target (stackSpell g "Cast Away Doubt")])
  inGraveyard g me "Cast Away Doubt" && life g me == 20
#guard
  let g := shockOnStack afterDraw
  castRejected g preciseRedaction [.target (stackSpell g "Shock")]

/- Sphinx's Approach draws two; with four other cards named Sphinx's Approach
in the graveyard, exiling all five finds a Sphinx creature card. -/
def approachGraveyard : Game :=
  let g := addToLibraryTop afterDraw sphinxOfFalseConclusions me
  let g := addToLibraryTop (addToLibraryTop g forest me) forest me
  (List.range 4).foldl (fun g _ => addToGraveyard g sphinxsApproach me) g

#guard
  let before := handSize approachGraveyard me
  let g := passBoth (castFra approachGraveyard sphinxsApproach)
  handSize g me == before + 2 &&
    (match g.pending with | .fraChoice _ (.sphinxsApproach _) => true | _ => false)
#guard
  let g := passBoth (castFra approachGraveyard sphinxsApproach)
  let g := mustApply g me .accept
  let g := applyIdle g
  onBattlefield g "Sphinx of False Conclusions" &&
    (g.objects.filter (fun o => o.zone == .exile && o.name == "Sphinx's Approach")).size == 5
#guard
  let g := resolved (castFra afterDraw sphinxsApproach)
  g.pending == .none

/- Unsummon returns a creature to its owner's hand. -/
#guard
  let g := resolved (castFra withBears unsummon [tgt withBears "Grizzly Bears"])
  inHand g opp "Grizzly Bears"

/- Unwind History (Diviner of Victory's prepare spell) returns a creature an
opponent controls with mana value 3 or less, then surveils 1. -/
#guard divinerOfVictory.prepareFace.any (·.spellEffect == some Effect.unwindHistory)
#guard
  let g := withBears.applyEffect me Effect.unwindHistory #[perm withBears "Grizzly Bears"]
  inHand g opp "Grizzly Bears" && g.pending == .surveil me 1

/- Arc of Fortune (Variable Chaser): each player may discard their hand and
draw seven, in turn order. -/
#guard variableChaser.prepareFace.any (·.spellEffect == some Effect.arcOfFortune)
#guard
  let g := afterDraw.applyEffect me Effect.arcOfFortune #[]
  let g := mustApply g me .accept
  let g := mustApply g opp .decline
  handSize g me == 7 && handSize g opp == handSize afterDraw opp &&
    (g.player me).graveyard.size == handSize afterDraw me

/-! ## Black -/

#guard
  let g := resolved (castFra afterDraw castAwayDoubt)
  life g me == 18 && life g opp == 18 && handSize g me == handSize afterDraw me + 2

#guard
  let g := resolved (castFra withBears extendedAbsence [tgt withBears "Grizzly Bears"])
  inExile g "Grizzly Bears" && life g opp == 19 && life g me == 21

/- Extrapolate the Impossible: reveal two cards with different names from
outside the game; an opponent chooses one for your hand. -/
def withSideboard : Game :=
  let g := insertObject afterDraw hillGiant me (.outside me)
  insertObject g crawWurm me (.outside me)

#guard
  let g := passBoth (castFra withSideboard extrapolateTheImpossible)
  let outside := (g.objects.filter (·.zone == .outside me)).map (·.id)
  let g := mustApply g me (.choosePermanents outside)
  match g.pending with
  | .fraChoice q (.extrapolatePick _ ids) =>
    q == opp &&
      let g := mustApply g opp (.choosePermanents (ids.extract 0 1))
      inHand g me "Hill Giant" && (g.objects.any (fun o => o.zone == .outside me && o.name == "Craw Wurm"))
  | _ => false
#guard
  let g := resolved (castFra afterDraw extrapolateTheImpossible)
  handSize g me == handSize afterDraw me
/- Ruling 774: the card that isn't chosen stays outside the game (checked
above: Craw Wurm is still outside). Ruling 775: cards outside the game are
the deck list's sideboard, which a game puts outside the game. -/
#guard (fraRuling 774).comment.contains "stays outside the game"
#guard (fraRuling 775).comment.contains "must come from your sideboard"
#guard
  let a : Seat := { name := "A", deck := Array.replicate 60 forest, sideboard := #[hillGiant, crawWurm] }
  let b : Seat := { name := "B", deck := Array.replicate 60 forest }
  match Start.start { seats := #[a, b], startingPlayer := some 0 } with
  | .ok g =>
    (g.player ⟨0⟩).sideboard.size == 2 &&
      ((g.materializeSideboard ⟨0⟩).objects.filter (·.zone == .outside ⟨0⟩)).size == 2
  | .error _ => false

#guard
  let g := addPermanent withBears grizzlyBears me me
  let g := addPermanent g hillGiant opp opp
  let g := resolved (castFra g overwriteTheMultiverse)
  !g.battlefield.any (·.isCreature) && (jaceTokenOf g).status.loyaltyCounters == 3

#guard
  let g := addToGraveyard afterDraw jaceRealitySculptor me
  let g := resolved (castFra g rewriteRegrets [gyTarget g me "Jace, Reality Sculptor"])
  (namedPermanent g "Jace, Reality Sculptor").status.loyaltyCounters == 5 &&
    (jaceTokenOf g).status.loyaltyCounters == 2

/- Rise of the Deathbringer: draw cards equal to the greatest power among your
creatures and lose that much life, or all creatures get minus three. -/
#guard
  let g := addPermanent afterDraw crawWurm me me
  let before := handSize g me
  let g := resolved (castFra g riseOfTheDeathbringer [.chooseMode 0])
  handSize g me == before + 6 && life g me == 14
#guard
  let g := addPermanent withGiant crawWurm me me
  let g := resolved (castFra g riseOfTheDeathbringer [.chooseMode 1])
  !onBattlefield g "Hill Giant" && g.toughness (namedPermanent g "Craw Wurm") == 1

/- Silence the Echo: the additional cost is sacrificing a creature or
planeswalker or paying {3}. -/
#guard silenceTheEcho.additionalCostSacrificeCreatureOrPlaneswalker &&
  silenceTheEcho.additionalCostOrPayGeneric == some 3
#guard
  let g := (withBears.empowerJace me 2)
  let g := castFra g silenceTheEcho [.chooseAdditionalCost false, tgt g "Grizzly Bears"]
  let g := mustApply g me (.sacrifice (jaceTokenOf g).id)
  let g := resolved g
  !onBattlefield g "Grizzly Bears" && (g.jacePlaneswalkerTokens me).isEmpty

/- Solve for Disappointment: you choose a nonland permanent card from the
target opponent's revealed hand. -/
#guard
  let g := addToHand afterDraw grizzlyBears opp
  let g := passBoth (castFra g solveForDisappointment [.target (.player opp)])
  let bears := handCardNamed g opp "Grizzly Bears"
  let g := mustApply g me (.choosePermanents #[bears.id])
  inGraveyard g opp "Grizzly Bears" && (jaceTokenOf g).status.loyaltyCounters == 1

#guard
  let g := resolved (castFra withGiant terminalCriticism [tgt withGiant "Hill Giant"])
  !onBattlefield g "Hill Giant" && life g me == 21
#guard castRejected withBears terminalCriticism [tgt withBears "Grizzly Bears"]

/- Vraska's Final Mercy: each mode keeps its own wording; only the second
mode empowers Jace. -/
#guard vraskasFinalMercy.empowerJace.isNone
#guard
  let g := resolved (castFra withBears vraskasFinalMercy [.chooseMode 0, tgt withBears "Grizzly Bears"])
  !onBattlefield g "Grizzly Bears" && life g me == 18 && (g.jacePlaneswalkerTokens me).isEmpty
#guard
  let g := resolved (castFra afterDraw vraskasFinalMercy [.chooseMode 1])
  life g me == 18 && (jaceTokenOf g).status.loyaltyCounters == 6

/-! ## Red -/

#guard
  let g := addPermanent afterDraw grizzlyBears me me
  let g := resolved (castFra g artifistAcumen)
  g.hasFirstStrike (namedPermanent g "Grizzly Bears") && handSize g me == handSize afterDraw me + 1

/- Awaken the Inferno: 6 damage to a creature or planeswalker an opponent
controls, and a +1/+1 counter on up to one creature you control. -/
#guard
  let g := addPermanent afterDraw crawWurm opp opp
  let g := addPermanent g grizzlyBears me me
  let g := resolved (castFra g awakenTheInferno [tgt g "Craw Wurm", tgt g "Grizzly Bears"])
  !onBattlefield g "Craw Wurm" && counters g "Grizzly Bears" == 1
#guard
  let g := addPermanent afterDraw crawWurm opp opp
  let g := resolved (castFra g awakenTheInferno [tgt g "Craw Wurm", .decline])
  !onBattlefield g "Craw Wurm"

/- Command the Stage creates a Cadet, then puts a counter on each other Wizard
token. -/
#guard
  let g := afterDraw.createKindTokens me .cadet 1
  let g := resolved (castFra g commandTheStage)
  creaturesNamed g "Cadet" == 2 &&
    (g.battlefield.filter (fun o => o.name == "Cadet" && o.status.plusOnePlusOne == 1)).size == 1

/- Essence Burn exiles the creature if it would die this turn. -/
#guard
  let g := resolved (castFra withBears essenceBurn [tgt withBears "Grizzly Bears"])
  inExile g "Grizzly Bears" && !inGraveyard g opp "Grizzly Bears"
#guard castRejected withGiant essenceBurn [tgt withGiant "Hill Giant"]

/- Fulminous Forte: 1 damage to each creature and planeswalker your opponents
control, or 5 damage to a creature or planeswalker. -/
#guard
  let g := addPermanent (enterPermanent afterDraw jaceRealitySculptor opp) ragingGoblin opp opp
  let g := addPermanent g ragingGoblin me me
  let g := resolved (castFra g fulminousForte [.chooseMode 0])
  (namedPermanent g "Jace, Reality Sculptor").status.loyaltyCounters == 4 &&
    (g.permanentsOf opp).all (·.name != "Raging Goblin") && onBattlefield g "Raging Goblin"
#guard
  let g := resolved (castFra withGiant fulminousForte [.chooseMode 1, tgt withGiant "Hill Giant"])
  !onBattlefield g "Hill Giant"

/- Wrath of the Bloodmane costs {1} less with a legendary creature. -/
#guard
  let g := addToHand withGiant wrathOfTheBloodmane me
  let card := handCardNamed g me "Wrath of the Bloodmane"
  let plain := g.playManaCost card card.printed
  let g := addPermanent g yurikoHopeFromTheShadows me me
  let card := handCardNamed g me "Wrath of the Bloodmane"
  (g.playManaCost card card.printed).manaValue + 1 == plain.manaValue
#guard
  let g := resolved (castFra withGiant wrathOfTheBloodmane [tgt withGiant "Hill Giant"])
  !onBattlefield g "Hill Giant"

/- Molten Tide (Pyre Rhymer): until end of turn, a Mountain tapped for mana
adds an additional {R}. -/
#guard pyreRhymer.prepareFace.any (·.spellEffect == some Effect.moltenTide)
#guard
  let g := addPermanent afterDraw mountain me me
  let g := g.applyEffect me Effect.moltenTide #[]
  let g := mustApply g me (.tapForMana (namedPermanent g "Mountain").id (.colored .red))
  (g.player me).manaPool.get (.colored .red) == 2

/-! ## Green -/

#guard carnivorousCultivator.prepareFace.any (·.spellEffect == some Effect.enroot)
#guard
  let g := applyIdle (afterDraw.applyEffect me Effect.enroot #[])
  (g.player me).graveyard.any (fun id => (g.object! id).printed.isLand)

/- Flourishing Grapple: a red or white creature or planeswalker an opponent
controls loses all abilities; your creature deals damage equal to its power
to it. -/
#guard
  let g := addPermanent withGiant crawWurm me me
  let g := resolved (castFra g flourishingGrapple [tgt g "Hill Giant", tgt g "Craw Wurm"])
  !onBattlefield g "Hill Giant" && (namedPermanent g "Craw Wurm").status.damage == 0
#guard
  let g := addPermanent withBears crawWurm me me
  castRejected g flourishingGrapple [tgt g "Grizzly Bears"]

#guard
  let g := addToGraveyard afterDraw hillGiant me
  let g := resolved (castFra g restoreWithEmpathy [gyTarget g me "Hill Giant"])
  inHand g me "Hill Giant" && life g me == 24

#guard
  let g := addToLibraryTop afterDraw grizzlyBears me
  let g := passBoth (castFra g somethingWorthSaving)
  match g.pending with
  | .fraChoice _ (.mayPutMilledPermanent ids 1) =>
    let bears := ids.find? (fun id => (g.object! id).name == "Grizzly Bears")
    let g := mustApply g me (.choosePermanents #[bears.get!])
    inHand g me "Grizzly Bears" && life g me == 21
  | _ => false

#guard
  let g := addPermanent afterDraw grizzlyBears me me
  let g := g.mapObjectStatus (namedPermanent g "Grizzly Bears") (fun s => { s with tapped := true })
  let g := resolved (castFra g tethermagesAdvantage [tgt g "Grizzly Bears"])
  let o := namedPermanent g "Grizzly Bears"
  g.power o == 4 && g.toughness o == 4 && !o.status.tapped && (g.currentKeywords o).reach

/-! ## Multicolor -/

#guard
  let g := addPermanent afterDraw grizzlyBears me me
  let g := resolved (castFra g chargeTheSanctum [.chooseMode 0])
  g.power (namedPermanent g "Grizzly Bears") == 4
#guard
  let g := addPermanent afterDraw grizzlyBears me me
  let g := resolved (castFra g chargeTheSanctum [.chooseMode 1, tgt g "Grizzly Bears"])
  let o := namedPermanent g "Grizzly Bears"
  g.power o == 5 && o.status.plusOnePlusOne == 1 && g.hasFirstStrike o

/- Clash of Elements: the owner puts the permanent on top of their library
and is dealt 2 damage, or puts it on the bottom. -/
#guard
  let g := passBoth (castFra withGiant clashOfElements [tgt withGiant "Hill Giant"])
  let g := mustApply g opp .chooseTop
  life g opp == 18 &&
    ((g.player opp).library.back?.map (fun id => (g.object! id).name)) == some "Hill Giant"
#guard
  let g := passBoth (castFra withGiant clashOfElements [tgt withGiant "Hill Giant"])
  let g := mustApply g opp .chooseBottom
  life g opp == 20 &&
    ((g.player opp).library[0]?.map (fun id => (g.object! id).name)) == some "Hill Giant"

/- Entrust the Spark: sacrifice a planeswalker to search for one. -/
#guard
  let g := addToLibraryTop (afterDraw.empowerJace me 1) jaceRealitySculptor me
  let g := passBoth (castFra g entrustTheSpark)
  let g := mustApply g me (.choosePermanents #[(jaceTokenOf g).id])
  let g := applyIdle g
  onBattlefield g "Jace, Reality Sculptor" && (g.jacePlaneswalkerTokens me).isEmpty

/- Fatehold Charm: draw and empower Jace 2 (only that mode empowers), bounce a
spell or creature, or creatures you control get +1/+2. -/
#guard fateholdCharm.empowerJace.isNone
#guard
  let g := resolved (castFra afterDraw fateholdCharm [.chooseMode 0])
  (jaceTokenOf g).status.loyaltyCounters == 2 && handSize g me == handSize afterDraw me + 1
#guard
  let g := shockOnStack afterDraw
  let g := resolved (castFra g fateholdCharm [.chooseMode 1, .target (stackSpell g "Shock")])
  inHand g me "Shock" && life g opp == 20
#guard
  let g := resolved (castFra withBears fateholdCharm [.chooseMode 1, tgt withBears "Grizzly Bears"])
  inHand g opp "Grizzly Bears"

/- Konstrari Charm: 6 damage to a creature with flying, two counters and
trample, or add {C}{C}{C}. -/
#guard
  let g := addPermanent afterDraw sphinxOfFalseConclusions opp opp
  let g := resolved (castFra g konstrariCharm [.chooseMode 0, tgt g "Sphinx of False Conclusions"])
  inGraveyard g opp "Sphinx of False Conclusions"
#guard
  let g := addPermanent afterDraw grizzlyBears me me
  let g := resolved (castFra g konstrariCharm [.chooseMode 1, tgt g "Grizzly Bears"])
  counters g "Grizzly Bears" == 2 && g.hasTrample (namedPermanent g "Grizzly Bears")
#guard
  let g := passBoth (castFra afterDraw konstrariCharm [.chooseMode 2])
  (g.player me).manaPool.get .colorless == 3

/- Recursive Recruitment: two Cadets; cast from a graveyard, each gets a
counter for every three cards in your graveyard. -/
#guard
  let g := resolved (castFra afterDraw recursiveRecruitment)
  creaturesNamed g "Cadet" == 2 && g.battlefield.all (·.status.plusOnePlusOne == 0)
#guard
  let g := (List.range 6).foldl (fun g _ => addToGraveyard g grizzlyBears me) afterDraw
  let g := everyColor (addToGraveyard g recursiveRecruitment me) me 8
  let g := mustApply g me (.cast (graveyardCard g me "Recursive Recruitment").id)
  let g := resolved (mustApply g me .pay)
  (g.battlefield.filter (fun o => o.name == "Cadet" && o.status.plusOnePlusOne == 2)).size == 2

#guard
  let g := resolved (castFra afterDraw stingerquillCharm [.chooseMode 0, .target (.player opp)])
  life g opp == 17
#guard
  let g := addPermanent afterDraw grizzlyBears me me
  let g := resolved (castFra g stingerquillCharm [.chooseMode 1, tgt g "Grizzly Bears"])
  g.hasFirstStrike (namedPermanent g "Grizzly Bears") &&
    g.hasDeathtouch (namedPermanent g "Grizzly Bears")
#guard
  let g := resolved (castFra afterDraw stingerquillCharm [.chooseMode 2])
  g.hasHaste (namedPermanent g "Cadet")

#guard
  let g := addToHand (addToHand afterDraw grizzlyBears opp) mountain opp
  let g := passBoth (castFra g stingingVitriol [.target (.player opp)])
  let g := mustApply g me (.choosePermanents #[(handCardNamed g opp "Grizzly Bears").id])
  life g opp == 18 && inGraveyard g opp "Grizzly Bears" && inHand g opp "Mountain"

#guard
  let g := addPermanent afterDraw grizzlyBears me me
  let g := resolved (castFra g tamsResistance [tgt g "Grizzly Bears"])
  counters g "Grizzly Bears" == 1 && g.hasVigilance (namedPermanent g "Grizzly Bears") &&
    (jaceTokenOf g).status.loyaltyCounters == 4

#guard
  let g := castFra afterDraw hexhavenBattalion
  let g := castFra g theorixCharm [.chooseMode 0, .target (stackSpell g "Hexhaven Battalion")]
  let g := passBoth g
  match g.pending with
  | .payOrLetCounter p 2 _ => inGraveyard (resolved (mustApply g p .decline)) me "Hexhaven Battalion"
  | _ => false
#guard
  let g := resolved (castFra withBears theorixCharm [.chooseMode 1, tgt withBears "Grizzly Bears"])
  !onBattlefield g "Grizzly Bears"
#guard
  let g := resolved (castFra afterDraw theorixCharm [.chooseMode 2])
  (g.player me).graveyard.size == 4 && handSize g me == handSize afterDraw me + 1

/- Twinned Vision draws one from hand, two with flashback (which also
requires discarding a card). -/
#guard twinnedVision.flashbackDiscard
#guard
  let g := resolved (castFra afterDraw twinnedVision)
  handSize g me == handSize afterDraw me + 1
#guard
  let g := everyColor (addToGraveyard afterDraw twinnedVision me) me
  let before := handSize g me
  let g := mustApply g me (.cast (graveyardCard g me "Twinned Vision").id)
  let g := mustApply g me .pay
  match g.pending with
  | .discardForAdditionalCost _ =>
    let g := mustApply g me (.discard (firstHandCard g me).id)
    let g := resolved g
    handSize g me == before - 1 + 2 && inExile g "Twinned Vision"
  | _ => false

#guard
  let g := addPermanent withBears grizzlyBears me me
  let theirs := (g.permanentsOf opp).find? (·.name == "Grizzly Bears") |>.get!
  let mine := (g.permanentsOf me).find? (·.name == "Grizzly Bears") |>.get!
  let g := resolved (castFra g twistedFates [.target (.permanent theirs.id), .target (.player me)])
  (g.findObject? theirs.id).isNone && (g.object! mine.id).status.plusOnePlusOne == 1

#guard
  let g := addPermanent afterDraw grizzlyBears me me
  let g := resolved (castFra g vigorbloomCharm [.chooseMode 0, tgt g "Grizzly Bears"])
  g.hasHexproof (namedPermanent g "Grizzly Bears") &&
    g.hasIndestructible (namedPermanent g "Grizzly Bears")
#guard
  let g := resolved (castFra afterDraw vigorbloomCharm [.chooseMode 1])
  life g me == 23 && handSize g me == handSize afterDraw me + 1
#guard
  let g := addPermanent withBears hillGiant me me
  let g := resolved (castFra g vigorbloomCharm [.chooseMode 2, tgt g "Hill Giant", tgt g "Grizzly Bears"])
  counters g "Hill Giant" == 1 && !onBattlefield g "Grizzly Bears"

/- Vindictive Triumph: a permanent with mana value 3 or less comes back tapped
under your control and is exiled at the next end step. -/
#guard
  let g := resolved (castFra withBears vindictiveTriumph [tgt withBears "Grizzly Bears"])
  let o := namedPermanent g "Grizzly Bears"
  o.controlledBy me && o.status.tapped &&
    let g := skipTo g .end 80
    inExile g "Grizzly Bears"
#guard
  let g := resolved (castFra withGiant vindictiveTriumph [tgt withGiant "Hill Giant"])
  inExile g "Hill Giant"

end Mtg.Engine.FraCardTests
