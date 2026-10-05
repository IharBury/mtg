import Mtg.Engine.FraCardTests

/-!
# Reality Fracture cards: triggered abilities

Game-state checks for every Reality Fracture triggered ability the parser
now models, including modal “choose one” triggers, reflexive triggers, and
triggers from a graveyard.
-/

namespace Mtg.Engine.FraCardTests2

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests
open Mtg.Engine.FraRulingTests
open Mtg.Engine.FraCardTests

/-- Put waiting triggers on the stack and resolve everything with default
choices. -/
def settle (g : Game) : Game := resolveStack (g.receivePriority g.activePlayer) 60

/-- Put waiting triggers on the stack (choosing targets by default) without
resolving them. -/
def stackTriggers (g : Game) : Game := g.receivePriority g.activePlayer

/-- Resolve the top of the stack. -/
def resolveTop (g : Game) : Game := passBoth g

def pendingFra (g : Game) : Option FraChoice :=
  match g.pending with
  | .fraChoice _ c => some c
  | _ => none

def tapped (g : Game) (name : String) : Game :=
  g.mapObjectStatus (namedPermanent g name) (fun s => { s with tapped := true })

def plusOnes (g : Game) (name : String) (n : Nat) : Game :=
  g.mapObjectStatus (namedPermanent g name) (fun s => { s with plusOnePlusOne := n })

def mine (g : Game) (name : String) : GameObject :=
  ((g.permanentsOf me).find? (·.name == name)).get!

def theirs (g : Game) (name : String) : GameObject :=
  ((g.permanentsOf opp).find? (·.name == name)).get!

/-- Attack with `names`, resolving attack triggers by default, then have the
opponent block with `blockers` and finish combat damage. -/
def attackThen (g : Game) (names : Array String)
    (blockers : Array (String × String) := #[]) : Game :=
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g me (.declareAttackers (names.map (fun n => (namedPermanent g n).id)))
  let g := skipToPending g .declareBlockers 80
  let g := mustApply g opp (.declareBlockers (blockers.map (fun (b, a) =>
    ((namedPermanent g b).id, (namedPermanent g a).id))))
  settle (skipTo g .postcombatMain 80)

def libraryTopName (g : Game) (p : PlayerId) : String :=
  ((g.player p).library.back?.map (fun id => (g.object! id).name)).getD ""

/- Every FRA triggered ability is modeled. -/
#guard [fateshaperAspirant, flickeringHound, guidingHydra, repurposedEnforcer,
    diviningDuelist, infiniteCoursework, planForAllOutcomes, seasonedCryomancer,
    sphinxOfFalseConclusions, apexWitchstalker, darkMatterManipulator, darklightPhoenix,
    rampartHunter, screechingSoulbreaker, chandrasEmberling, commandTheStage,
    craterclawColossus, curseMarredDemon, heartstringPuller, masterOfBarbs,
    stingcasterMage, tetherTechnician, carnivorousCultivator, greenhousePropagator,
    hexhavenInvigorator, inspiredTethermage, simulacrumShaper, vinelasherAdept,
    bloombrute, craftworkCrusher, denziloreFatehold, frostbitePyromental,
    mindMeanderer, primalWitchstalker, solariumSentry, uldarosTheorix,
    archiveArbiter, theEchoverseFulcrum, eyeOfJace, danithaSwordOfHope,
    saheeliConsulOfOversight, hapatraTheDesertFrost, lyraTolarianArchangel,
    yurikoHopeFromTheShadows, lilianaTheRepentant, mabelBitterRecluse,
    massacreGirlMostWanted, tinybonesPocketNuisance, wayOfTheNecromancer,
    winterTormentedLoner, arniRenownedChampion, jiangYangguAlone, kothTheGeomancer,
    tetsukoUmezawaPursuer, edgarMoonlitSovereign, garrukCurseBreaker,
    jiangYangguNeverAlone, piaAetherAscetic, wayOfTheParadox, yoshimaruScrappyStray,
    edgarAncientBloodlord, hapatraTheDesertFang, karnGildedGuardian, mabelValleyHero,
    saheeliJewelOfAvishkar].all (fun c =>
  c.staticAbilities.all (fun
    | .printed s => !(s.startsWith "When" || s.startsWith "At the")
    | _ => true))

/-! ## Cast triggers -/

/- Emrakul: when you cast it, untap all lands you control. -/
#guard
  let g := tapped (addPermanent afterDraw forest me me) "Forest"
  let g := castFra g emrakulTheExigentDoom
  let g := resolveTop g
  !(namedPermanent g "Forest").status.tapped

/- Chandra's Emberling gets a counter for each noncreature spell. -/
#guard
  let g := addPermanent afterDraw chandrasEmberling me me
  let g := resolved (castFra g shock [.target (.player opp)])
  counters g "Chandra's Emberling" == 1

/- Danitha, Sword of Hope draws once each turn for a spell that targets your
creature. -/
#guard
  let g := addPermanent (addPermanent afterDraw danithaSwordOfHope me me) grizzlyBears me me
  let before := handSize g me
  let g := resolved (castFra g giantGrowth [tgt g "Grizzly Bears"])
  let g := resolved (castFra g giantGrowth [tgt g "Grizzly Bears"])
  handSize g me == before + 1

/- Saheeli, Jewel of Avishkar makes a Thopter for each noncreature spell. -/
#guard
  let g := addPermanent afterDraw saheeliJewelOfAvishkar me me
  let g := resolved (castFra g shock [.target (.player opp)])
  creaturesNamed g "Thopter" == 1

/- Traxos untaps when you cast an artifact or creature spell. -/
#guard
  let g := tapped (addPermanent afterDraw traxosScourgeEternal me me) "Traxos, Scourge Eternal"
  let g := resolved (castFra g grizzlyBears)
  !(namedPermanent g "Traxos, Scourge Eternal").status.tapped

/- Solarium Sentry: an opponent's spell with mana value 2 or less gains you 2. -/
#guard
  let g := addPermanent afterDraw solariumSentry me me
  let g := mustApply g me .pass
  let g := resolved (castFra g shock [.target (.player me)] opp)
  (g.player me).lifeGainedThisTurn == 2 && life g me == 20

/- Flickering Hound blinks another creature you control when you cast a
creature spell; it returns untapped with no counters. -/
#guard
  let g := addPermanent (addPermanent afterDraw flickeringHound me me) hillGiant me me
  let g := plusOnes (tapped g "Hill Giant") "Hill Giant" 2
  let g := castFra g grizzlyBears
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (tgt g "Hill Giant")
    | _ => g
  let g := resolved g
  let giant := namedPermanent g "Hill Giant"
  !giant.status.tapped && giant.status.plusOnePlusOne == 0

/- Codie copies a prepared spell when you cast it. -/
#guard
  let g := addPermanent withBears codieRavenousCodex me me
  let g := enterPermanent g divinerOfVictory me
  let copy := (exiledCopies g "Unwind History")[0]!
  let g := everyColor g me
  let g := mustApply g me (.cast copy.id)
  let g := mustApply g me (tgt g "Grizzly Bears")
  let g := mustApply g me .pay
  let g := stackTriggers g
  let g := resolveTop g
  logContains g "A copy of Unwind History is created"

/-! ## Enters triggers -/

/- Fateshaper Aspirant: modes are chosen as the trigger goes on the stack. -/
#guard
  let g := addPermanent afterDraw grizzlyBears me me
  let g := stackTriggers (enterPermanent g fateshaperAspirant me)
  match pendingFra g with
  | some (.triggerModes _ 1 _) =>
    let g := mustApply g me (.chooseMode 1)
    let g := match g.pending with
      | .chooseTargets _ => mustApply g me (tgt g "Grizzly Bears")
      | _ => g
    let g := resolved g
    counters g "Grizzly Bears" == 1 && g.hasVigilance (namedPermanent g "Grizzly Bears") &&
      g.hasIndestructible (namedPermanent g "Grizzly Bears")
  | _ => false
#guard
  let g := addToGraveyard afterDraw yurikoHopeFromTheShadows me
  let g := stackTriggers (enterPermanent g fateshaperAspirant me)
  let g := mustApply g me (.chooseMode 0)
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (gyTarget g me "Yuriko, Hope from the Shadows")
    | _ => g
  inHand (resolved g) me "Yuriko, Hope from the Shadows"

/- Divining Duelist taps a creature. -/
#guard
  let g := stackTriggers (enterPermanent withBears diviningDuelist me)
  let g := mustApply g me (.chooseMode 0)
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (tgt g "Grizzly Bears")
    | _ => g
  (namedPermanent (resolved g) "Grizzly Bears").status.tapped

/- Archive Arbiter: gain 4 life. -/
#guard
  let g := stackTriggers (enterPermanent afterDraw archiveArbiter me)
  life (resolved (mustApply g me (.chooseMode 1))) me == 24

/- Yuriko, Hope from the Shadows: target creature gets minus X power, X =
cards in your graveyard. -/
#guard
  let g := (List.range 2).foldl (fun g _ => addToGraveyard g forest me) withGiant
  let g := stackTriggers (enterPermanent g yurikoHopeFromTheShadows me)
  let g := mustApply g me (.chooseMode 0)
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (tgt g "Hill Giant")
    | _ => g
  g.power (namedPermanent (resolved g) "Hill Giant") == 1

/- Craftwork Crusher chooses two modes (ruling 803: the damage mode's target
being illegal stops the whole ability). -/
#guard
  let g := withGiant
  let before := handSize g me
  let g := stackTriggers (enterPermanent g craftworkCrusher me)
  let g := mustApply g me (.chooseMode 0)
  let g := mustApply g me (.chooseMode 2)
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (tgt g "Hill Giant")
    | _ => g
  let g := resolved g
  !onBattlefield g "Hill Giant" && handSize g me == before + 1
#guard
  let g := stackTriggers (enterPermanent withGiant craftworkCrusher me)
  let g := mustApply g me (.chooseMode 0)
  let g := mustApply g me (.chooseMode 2)
  let g := mustApply g me (tgt g "Hill Giant")
  let before := handSize g me
  let g := g.destroyPermanent (namedPermanent g "Hill Giant")
  let g := resolved g
  handSize g me == before
#guard (fraRuling 803).comment.contains "none of its other effects will happen"

/- Infinite Coursework taps the enchanted creature and unprepares it. -/
#guard
  let g := enterPermanent afterDraw divinerOfVictory me
  let host := namedPermanent g "Diviner of Victory"
  let (g, aura) := g.allocObject infiniteCoursework me .battlefield (some me) (attachedTo := some host.id)
  let g := settle (g.afterPermanentEnters aura)
  let o := namedPermanent g "Diviner of Victory"
  o.status.tapped && !o.status.prepared

/- Plan for All Outcomes: the owner chooses top or bottom. -/
#guard
  let g := stackTriggers (enterPermanent withBears planForAllOutcomes me)
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (tgt g "Grizzly Bears")
    | _ => g
  let g := resolveTop g
  let g := mustApply g opp .chooseTop
  libraryTopName g opp == "Grizzly Bears"

/- Seasoned Cryomancer: draw two, discard two; one nonland discarded lets it
stun one creature. -/
#guard
  let g := addToHand (addToHand withGiant grizzlyBears me) forest me
  let g := resolveTop (stackTriggers (enterPermanent g seasonedCryomancer me))
  let bears := handCardNamed g me "Grizzly Bears"
  let forestCard := handCardNamed g me "Forest"
  let g := mustApply g me (.choosePermanents #[bears.id, forestCard.id])
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (.targets #[perm g "Hill Giant"])
    | _ => g
  let g := resolved g
  let giant := namedPermanent g "Hill Giant"
  giant.status.tapped && giant.status.stun == 1

/- Apex Witchstalker gains 2 when it enters and when it dies. -/
#guard
  let g := settle (enterPermanent afterDraw apexWitchstalker me)
  let g := settle (g.destroyPermanent (namedPermanent g "Apex Witchstalker"))
  life g me == 24

/- Dark Matter Manipulator mills three. -/
#guard (settle (enterPermanent afterDraw darkMatterManipulator me) |>.player me).graveyard.size == 3

/- Lich's Relic: pay {2}; when you do, destroy up to one target creature or
planeswalker each opponent controls. -/
#guard
  let g := stackTriggers (enterPermanent withBears lichsRelic me)
  let g := resolveTop g
  let g := withMana g me .black 2
  let g := mustApply g me .accept
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (tgt g "Grizzly Bears")
    | _ => g
  !onBattlefield (resolved g) "Grizzly Bears"

#guard
  let g := addPermanent afterDraw grizzlyBears me me
  let g := settle (enterPermanent g rampartHunter me)
  g.power (namedPermanent g "Grizzly Bears") == 4 && g.hasDeathtouch (namedPermanent g "Grizzly Bears")

/- Ajani's Anguish deals X damage, X as cast. -/
#guard
  let g := castFra afterDraw ajanisAnguish [.chooseX 3]
  let g := resolveTop g
  let g := stackTriggers g
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (.target (.player opp))
    | _ => g
  life (resolved g) opp == 17

/- Craterclaw Colossus: creatures gain trample and +X/+0 for artifacts. -/
#guard
  let g := addPermanent (addPermanent afterDraw codieRavenousCodex me me) grizzlyBears me me
  let g := settle (enterPermanent g craterclawColossus me)
  g.power (namedPermanent g "Grizzly Bears") == 4 &&
    g.hasTrample (namedPermanent g "Grizzly Bears")

/- Curse-Marred Demon: tutor, then discard at random. -/
#guard
  let g := settle (enterPermanent afterDraw curseMarredDemon me)
  handSize g me == handSize afterDraw me && (g.player me).graveyard.size == 1

#guard creaturesNamed (settle (enterPermanent afterDraw heartstringPuller me)) "Cadet" == 1
#guard (settle (enterPermanent afterDraw hungeringPuppetbeast me)).battlefield.any (·.name == "Heartwood")

/- Stingcaster Mage gives an instant in your graveyard flashback this turn. -/
#guard
  let g := addToGraveyard afterDraw shock me
  let g := settle (enterPermanent g stingcasterMage me)
  let g := everyColor g me
  let g := mustApply g me (.cast (graveyardCard g me "Shock").id)
  let g := mustApply g me (.target (.player opp))
  let g := resolved (mustApply g me .pay)
  life g opp == 18 && inExile g "Shock"

/- Tether Technician: discard a card; when you do, 2 damage to any target. -/
#guard
  let g := addToHand afterDraw forest me
  let g := resolveTop (stackTriggers (enterPermanent g tetherTechnician me))
  let g := mustApply g me (.choosePermanents #[(handCardNamed g me "Forest").id])
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (.target (.player opp))
    | _ => g
  life (resolved g) opp == 18

/- Simulacrum Shaper may search for a basic land tapped. -/
#guard
  let g := resolveTop (stackTriggers (enterPermanent afterDraw simulacrumShaper me))
  let lands := (afterDraw.permanentsOf me).size
  let g := mustApply g me .accept
  (g.permanentsOf me).size == lands + 2

#guard
  let g := addPermanent afterDraw grizzlyBears me me
  let g := stackTriggers (enterPermanent g vinelasherAdept me)
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (tgt g "Grizzly Bears")
    | _ => g
  counters (resolved g) "Grizzly Bears" == 3

/- Aerid Konstrari makes a Heartwood when it enters and when it dies. -/
#guard
  let g := settle (enterPermanent afterDraw aeridKonstrari me)
  let g := settle (g.destroyPermanent (namedPermanent g "Aerid Konstrari"))
  (g.battlefield.filter (·.name == "Heartwood")).size == 2

/- Mind Meanderer fights up to one creature an opponent controls. -/
#guard
  let g := stackTriggers (enterPermanent withBears mindMeanderer me)
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (tgt g "Grizzly Bears")
    | _ => g
  !onBattlefield (resolved g) "Grizzly Bears"

/- Null Summoner exiles a nonland card from the opponent's hand if you cast
it; with seven or more cards in your graveyard you may cast that card with
mana of any type. -/
#guard
  let g := addToHand afterDraw hillGiant opp
  let g := castFra g nullSummoner
  let g := resolveTop g
  let g := stackTriggers g
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (.target (.player opp))
    | _ => g
  let g := resolveTop g
  let g := mustApply g me (.choosePermanents #[(handCardNamed g opp "Hill Giant").id])
  let exiled := (g.objects.find? (fun o => o.zone == .exile && o.name == "Hill Giant")).get!
  let g := (List.range 7).foldl (fun g _ => addToGraveyard g forest me) g
  g.mayPlay me exiled && !g.mayPlay opp exiled
#guard
  let g := settle (enterPermanent (addToHand afterDraw hillGiant opp) nullSummoner me)
  inHand g opp "Hill Giant"

/- Primal Witchstalker: mill four; when you do, return a land card tapped. -/
#guard
  let g := addToLibraryTop afterDraw forest me
  let lands := ((g.permanentsOf me).filter (·.printed.isLand)).size
  let g := settle (enterPermanent g primalWitchstalker me)
  ((g.permanentsOf me).filter (fun o => o.printed.isLand && o.status.tapped)).size == lands + 1

/- Proctor of Potential surveils when it or another creature enters. -/
#guard
  let g := stackTriggers (enterPermanent afterDraw proctorOfPotential me)
  let g := resolveTop g
  g.pending == .surveil me 1

/- Solitary Cell exiles a nonland permanent until it leaves. -/
#guard
  let g := stackTriggers (enterPermanent withBears solitaryCell me)
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (tgt g "Grizzly Bears")
    | _ => g
  let g := resolved g
  inExile g "Grizzly Bears" &&
    let g := g.destroyPermanent (namedPermanent g "Solitary Cell")
    onBattlefield g "Grizzly Bears"

/- Tenured Tethermage: sacrifice a land for two tapped Heartwoods. -/
#guard
  let g := addPermanent afterDraw forest me me
  let g := resolveTop (stackTriggers (enterPermanent g tenuredTethermage me))
  let g := mustApply g me (.choosePermanents #[(namedPermanent g "Forest").id])
  (g.battlefield.filter (fun o => o.name == "Heartwood" && o.status.tapped)).size == 2

/- Uldaros Theorix: exile up to one card of each type from your graveyard,
copy them, and cast copies with total mana value 6 or less free. Ruling 806:
X is 0. -/
#guard
  let g := addToGraveyard (addToGraveyard afterDraw shock me) grizzlyBears me
  let g := castFra g uldarosTheorix
  let g := resolveTop g
  let g := stackTriggers g
  let shockCard := graveyardCard g me "Shock"
  let bearsCard := graveyardCard g me "Grizzly Bears"
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (.targets #[.card bearsCard.id, .card shockCard.id])
    | _ => g
  let g := resolveTop g
  match pendingFra g with
  | some (.castCopiesFree ids 6 _) =>
    let shockCopy := (ids.find? (fun id => (g.object! id).name == "Shock")).get!
    let g := mustApply g me (.cast shockCopy)
    let g := mustApply g me (.target (.player opp))
    let g := resolved g
    life g opp == 18 && inExile g "Shock" && inExile g "Grizzly Bears"
  | _ => false
#guard (fraRuling 806).comment.contains "you must choose 0 as the value for X"

/- Warrior's Blades deals 3 and gains 3. -/
#guard
  let g := stackTriggers (enterPermanent afterDraw warriorsBlades me)
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (.target (.player opp))
    | _ => g
  let g := resolved g
  life g opp == 17 && life g me == 23

#guard
  let before := handSize afterDraw me
  let g := settle (enterPermanent afterDraw theEchoverseFulcrum me)
  handSize g me == before && (g.player me).graveyard.size == 1

/- Hapatra, the Desert Frost taps and stuns a creature each opponent controls. -/
#guard
  let g := stackTriggers (enterPermanent withGiant hapatraTheDesertFrost me)
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (tgt g "Hill Giant")
    | _ => g
  let giant := namedPermanent (resolved g) "Hill Giant"
  giant.status.tapped && giant.status.stun == 1

/- Mabel, Bitter Recluse removes up to three counters. -/
#guard
  let g := plusOnes withGiant "Hill Giant" 4
  let g := stackTriggers (enterPermanent g mabelBitterRecluse me)
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (tgt g "Hill Giant")
    | _ => g
  counters (resolved g) "Hill Giant" == 1

/- Winter: sacrifice a creature; each opponent sacrifices one. -/
#guard
  let g := addPermanent withBears grizzlyBears me me
  let g := resolveTop (stackTriggers (enterPermanent g winterTormentedLoner me))
  let g := mustApply g me (.choosePermanents #[(mine g "Grizzly Bears").id])
  let g := match g.pending with
    | .chooseSacrificeCreature q _ _ => mustApply g q (.sacrifice (theirs g "Grizzly Bears").id)
    | _ => g
  !(g.permanentsOf opp).any (·.name == "Grizzly Bears")

#guard creaturesNamed (settle (enterPermanent afterDraw kioraOfFireAndAshes me)) "Dragon" == 1
#guard creaturesNamed (settle (enterPermanent afterDraw piaDeterminedRebuilder me)) "Thopter" == 1
#guard creaturesNamed (settle (enterPermanent afterDraw jiangYangguNeverAlone me)) "Mowu" == 1

/- Fblthp, Knows the Way finds up to X basic lands with different names. -/
#guard
  let g := addToLibraryTop (addToLibraryTop (addToLibraryTop afterDraw forest me) forest me) island me
  let g := castFra g fblthpKnowsTheWay [.chooseX 2]
  let before := handSize g me
  let g := resolved g
  handSize g me == before + 2

/- Pia, Aether Ascetic: discard a card to find an enchantment. -/
#guard
  let g := addToLibraryTop (addToHand afterDraw forest me) solitaryCell me
  let g := addToLibraryTop g ajanisAnguish me
  let g := resolveTop (stackTriggers (enterPermanent g piaAetherAscetic me))
  let g := mustApply g me (.choosePermanents #[(handCardNamed g me "Forest").id])
  inHand g me "Ajani's Anguish"

/- Yoshimaru, Scrappy Stray: another creature you control fights. -/
#guard
  let g := addPermanent withBears hillGiant me me
  let g := stackTriggers (enterPermanent g yoshimaruScrappyStray me)
  let g := match g.pending with
    | .chooseTargets _ =>
      let g := mustApply g me (tgt g "Hill Giant")
      mustApply g me (tgt g "Grizzly Bears")
    | _ => g
  !onBattlefield (resolved g) "Grizzly Bears"

/- Hapatra, the Desert Fang: minus-one counters equal to the greatest mana
value in your graveyard; they annihilate with +1/+1 counters (ruling 885). -/
#guard
  let g := plusOnes (addToGraveyard withGiant shock me) "Hill Giant" 1
  let g := addToGraveyard g grizzlyBears me
  let g := stackTriggers (enterPermanent g hapatraTheDesertFang me)
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (tgt g "Hill Giant")
    | _ => g
  let giant := namedPermanent (resolved g) "Hill Giant"
  giant.status.plusOnePlusOne == 0 && giant.status.minusOneMinusOne == 1
#guard (fraRuling 885).comment.contains "removed in pairs"

/- Graft Surgeon counts minus-one counters too (rulings 759 / 760). -/
#guard
  let g := addPermanent withBears graftSurgeon me me
  let g := g.mapObjectStatus (namedPermanent g "Graft Surgeon")
    (fun s => { s with minusOneMinusOne := 2 })
  let g := addPermanent g hillGiant me me
  let g := g.mapObjectStatus (namedPermanent g "Graft Surgeon")
    (fun s => { s with damage := 5 })
  let g := stackTriggers g.checkSBA
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (tgt g "Hill Giant")
    | _ => g
  (namedPermanent (resolved g) "Hill Giant").status.minusOneMinusOne == 2
#guard (fraRuling 759).comment.contains "-1/-1 counters on it when it dies"
#guard (fraRuling 760).comment.contains "-1/-1 counters are put on Graft Surgeon"

/- Karn, Gilded Guardian draws for each color among other artifacts. -/
#guard
  let g := addPermanent afterDraw codieRavenousCodex me me
  let before := handSize g me
  handSize (settle (enterPermanent g karnGildedGuardian me)) me == before

/-! ## Other creatures entering -/

#guard
  let g := addPermanent afterDraw greenhousePropagator me me
  life (settle (enterPermanent g grizzlyBears me)) me == 21
#guard
  let g := addPermanent afterDraw lilianaTheFaultless me me
  life (settle (enterPermanent g grizzlyBears me)) me == 21
#guard
  let g := addPermanent afterDraw lilianaTheRepentant me me
  ((settle (enterPermanent g grizzlyBears me)).player me).graveyard.size == 2
#guard
  let g := tapped (addPermanent afterDraw arniHumbleScribe me me) "Arni, Humble Scribe"
  !(namedPermanent (settle (enterPermanent g grizzlyBears me)) "Arni, Humble Scribe").status.tapped
#guard
  let g := addPermanent afterDraw arniRenownedChampion me me
  let g := settle (enterPermanent g hillGiant me)
  g.power (namedPermanent g "Arni, Renowned Champion") ==
    (arniRenownedChampion.power.getD 0) + 3
#guard
  let g := addPermanent afterDraw garrukCurseBreaker me me
  let before := handSize g me
  handSize (settle (enterPermanent g crawWurm me)) me == before + 1 &&
    handSize (settle (enterPermanent g grizzlyBears me)) me == before
#guard
  let g := addPermanent afterDraw mabelValleyHero me me
  let g := stackTriggers (enterPermanent g grizzlyBears me)
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (tgt g "Grizzly Bears")
    | _ => g
  counters (resolved g) "Grizzly Bears" == 1
/- Gideon the Oathless: an opponent's creature entering deals 1 to them. -/
#guard
  let g := addPermanent afterDraw gideonTheOathless me me
  life (settle (enterPermanent g grizzlyBears opp)) opp == 19

/-! ## Dies triggers -/

/- Sphinx of False Conclusions: a nontoken one dying makes a token copy. -/
#guard
  let g := addPermanent afterDraw sphinxOfFalseConclusions me me
  let g := settle (g.destroyPermanent (namedPermanent g "Sphinx of False Conclusions"))
  g.battlefield.any (fun o => o.name == "Sphinx of False Conclusions" && o.printed.isToken)

/- Ferocity of the Hunt returns the enchanted creature tapped. -/
#guard
  let g := addPermanent afterDraw grizzlyBears me me
  let host := namedPermanent g "Grizzly Bears"
  let (g, _) := g.allocObject ferocityOfTheHunt me .battlefield (some me) (attachedTo := some host.id)
  let g := settle (g.destroyPermanent (namedPermanent g "Grizzly Bears"))
  (namedPermanent g "Grizzly Bears").status.tapped

/- Massacre Girl, Edgar, and Way of the Necromancer see creatures die. -/
#guard
  let g := addPermanent (addPermanent afterDraw massacreGirlMostWanted me me) grizzlyBears me me
  let g := settle (g.destroyPermanent (namedPermanent g "Grizzly Bears"))
  life g opp == 19 && life g me == 21
#guard
  let g := addPermanent (addPermanent afterDraw edgarAncientBloodlord me me) grizzlyBears me me
  life (settle (g.destroyPermanent (namedPermanent g "Grizzly Bears"))) me == 21
#guard
  let g := addPermanent (afterDraw.empowerJace me 1) wayOfTheNecromancer me me
  let g := addPermanent g grizzlyBears me me
  let g := settle (g.destroyPermanent (namedPermanent g "Grizzly Bears"))
  (jaceTokenOf g).status.loyaltyCounters == 2

/- Massacre Girl gets a counter when an opponent is dealt noncombat damage;
Master of Barbs pumps your team. -/
#guard
  let g := addPermanent afterDraw massacreGirlMostWanted me me
  counters (settle (g.dealDamageToPlayer opp 1)) "Massacre Girl, Most Wanted" == 1
#guard
  let g := addPermanent (addPermanent afterDraw masterOfBarbs me me) grizzlyBears me me
  let g := settle (g.dealDamageToPlayer opp 1)
  g.power (namedPermanent g "Grizzly Bears") == 3

/-! ## Life, scry, discard, and loyalty triggers -/

#guard
  let g := addPermanent afterDraw bloombrute me me
  let before := handSize g me
  let g := settle ((settle (g.gainLife me 1)).gainLife me 1)
  handSize g me == before + 1
#guard
  let g := addPermanent afterDraw kwiaVigorbloom me me
  let g := settle ((settle (g.gainLife me 1)).gainLife me 1)
  (g.battlefield.filter (·.name == "Lotus")).size == 1
#guard
  let g := addPermanent (afterDraw.empowerJace me 1) wayOfTheMentor me me
  (jaceTokenOf (settle (g.gainLife me 1))).status.loyaltyCounters == 2
#guard
  let g := addPermanent (addPermanent afterDraw denziloreFatehold me me) grizzlyBears me me
  let g := settle (g.beginScry me 1)
  counters g "Grizzly Bears" == 1
#guard
  let g := addPermanent afterDraw saheeliConsulOfOversight me me
  let g := settle (settle (g.beginScry me 1) |>.beginScry me 1)
  creaturesNamed g "Thopter" == 1
#guard
  let g := addPermanent afterDraw inspiredTethermage me me
  counters (settle (g.empowerJace me 2)) "Inspired Tethermage" == 1
#guard
  let g := addPermanent afterDraw tinybonesPocketNuisance me me
  let g := addToHand g forest opp
  let g := g.discardFromHand opp (handCardNamed g opp "Forest").id
  life (settle g) opp == 19
#guard
  let g := addToHand afterDraw titanbonesToweringHeart me
  let g := g.discardFromHand me (handCardNamed g me "Titanbones, Towering Heart").id
  life (settle g) me == 23
/- Way of the Paradox and Gideon see loyalty abilities. -/
#guard
  let g := addPermanent (afterDraw.empowerJace me 2) wayOfTheParadox me me
  let g := mustApply g me (.activate (jaceTokenOf g).id 0)
  let g := resolved g
  life g me == 21 && (g.player me).additionalLandsThisTurn == 1
#guard
  let g := addPermanent (afterDraw.empowerJace opp 2) gideonTheOathless me me
  let g := skipTo (skipTo g .upkeep 400) .precombatMain 400
  let g := mustApply g opp (.activate (jaceTokenOf g opp).id 0)
  life (settle g) opp == 19

/-! ## Combat triggers -/

#guard
  let g := addPermanent (addPermanent afterDraw repurposedEnforcer me me) grizzlyBears me me
  let g := attackThen g #["Repurposed Enforcer"]
  (jaceTokenOf g).status.loyaltyCounters == 2
#guard
  let g := addPermanent afterDraw screechingSoulbreaker me me
  let g := (attackThen g #["Screeching Soulbreaker"])
  life g me == 21
#guard
  let g := addPermanent (addPermanent afterDraw ingrisStingerquill me me) grizzlyBears me me
  let g := (attackThen g #["Grizzly Bears"])
  life g opp == 17
#guard
  let g := addPermanent (addPermanent afterDraw yurikoBladeOfTheMighty me me) grizzlyBears me me
  let g := (attackThen g #["Grizzly Bears"])
  life g opp == 16
#guard
  let g := addPermanent (addToGraveyard afterDraw forest me) carnivorousCultivator me me
  let g := (attackThen g #["Carnivorous Cultivator"])
  inHand g me "Forest"
#guard
  let g := addPermanent (addToGraveyard afterDraw forest opp) afterthoughtSentry me me
  let g := (attackThen g #["Afterthought Sentry"])
  inExile g "Forest"
/- Jiang Yanggu, Alone: a creature attacking a player alone loots and grows
(ruling 861). -/
#guard
  let g := addPermanent (addPermanent (addToHand afterDraw forest me) jiangYangguAlone me me) grizzlyBears me me
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g me (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])
  let g := resolveTop (stackTriggers g)
  let g := mustApply g me (.choosePermanents #[(handCardNamed g me "Forest").id])
  counters g "Grizzly Bears" == 1
#guard (fraRuling 861).comment.contains "attacks a player alone"
/- Tetsuko Umezawa, Pursuer: a small blocker hurts its controller. -/
#guard
  let g := addPermanent (addPermanent afterDraw tetsukoUmezawaPursuer me me) ragingGoblin opp opp
  let g := attackThen g #["Tetsuko Umezawa, Pursuer"] #[("Raging Goblin", "Tetsuko Umezawa, Pursuer")]
  life g opp == 19
/- Hexhaven Invigorator: dealt damage, search for that many lands. -/
#guard
  let g := addPermanent afterDraw hexhavenInvigorator me me
  let lands := ((afterDraw.permanentsOf me).filter (·.printed.isLand)).size
  let g := resolveTop (stackTriggers (g.dealDamageToPermanent (namedPermanent g "Hexhaven Invigorator") 2))
  let g := mustApply g me .accept
  ((g.permanentsOf me).filter (·.printed.isLand)).size == lands + 2

/-! ## Step triggers -/

#guard
  let g := plusOnes (addPermanent (addPermanent afterDraw guidingHydra me me) grizzlyBears me me)
    "Guiding Hydra" 2
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g me .accept
  counters g "Grizzly Bears" == 1 && counters g "Guiding Hydra" == 1
#guard
  let g := addToGraveyard afterDraw darklightPhoenix me
  let g := { g with creatureDeathsThisTurn := 2 }
  let g := settle (skipTo g .beginningOfCombat 80)
  onBattlefield g "Darklight Phoenix"
#guard
  let g := addToGraveyard afterDraw commandTheStage me
  let g := settle (g.dealDamageToPlayer opp 1)
  let g := settle (skipTo g .upkeep 200)
  inHand g me "Command the Stage"
#guard
  let g := addPermanent afterDraw frostbitePyromental me me
  !onBattlefield (settle (skipTo g .end 80)) "Frostbite Pyromental"
#guard
  let g := addPermanent afterDraw lyraTolarianArchangel me me
  let g := settle ((g.draw me 3) |> (skipTo · .end 80))
  creaturesNamed g "Angel" == 1
#guard
  let g := addPermanent afterDraw edgarMoonlitSovereign me me
  counters (settle (skipTo g .end 80)) "Edgar, Moonlit Sovereign" == 2
#guard
  let g := settle (enterPermanent afterDraw jiangYangguNeverAlone me)
  let g := tapped g "Mowu"
  !(namedPermanent (settle (skipTo g .end 80)) "Mowu").status.tapped
/-- The next upkeep of `me`'s turn. -/
def myNextUpkeep (g : Game) : Game :=
  skipTo (skipTo (skipTo g .upkeep 400) .draw 400) .upkeep 400

#guard
  let g := (List.range 7).foldl (fun g _ => addToGraveyard g forest me)
    (addPermanent afterDraw eyeOfJace me me)
  let g := settle (myNextUpkeep g)
  !onBattlefield g "Eye of Jace" && life g me == 22 && life g opp == 18
#guard
  let g := settle (myNextUpkeep (addPermanent afterDraw eyeOfJace me me))
  onBattlefield g "Eye of Jace"

/-! ## Koth, the Geomancer -/

#guard
  let g := addPermanent (addToHand afterDraw mountain me) kothTheGeomancer me me
  let g := mustApply g me (.playLand (handCardNamed g me "Mountain").id)
  let g := stackTriggers g
  let g := resolveTop g
  life g opp == 19 && (g.player me).manaPool.get (.colored .red) == 1

/- Kiora of Salt and Sand untaps an attacker that can't be blocked if you
activated a loyalty ability this turn. -/
#guard
  let g := addPermanent (afterDraw.empowerJace me 2) kioraOfSaltAndSand me me
  let g := addPermanent g grizzlyBears me me
  let g := resolved (mustApply g me (.activate (jaceTokenOf g).id 0))
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g me (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])
  let g := stackTriggers g
  let g := match g.pending with
    | .chooseTargets _ => mustApply g me (tgt g "Grizzly Bears")
    | _ => g
  let g := resolveTop g
  !(namedPermanent g "Grizzly Bears").status.tapped

end Mtg.Engine.FraCardTests2
