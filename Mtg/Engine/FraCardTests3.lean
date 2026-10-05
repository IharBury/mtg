import Mtg.Engine.FraCardTests2

/-!
# Reality Fracture cards: activated, loyalty, and static abilities

Game-state checks for every Reality Fracture activated ability, loyalty
ability, and static ability, including Emrakul's granted mana ability
(rulings 729 / 730) and Tomik's limit on creatures attacking a planeswalker
(ruling 834).
-/

namespace Mtg.Engine.FraCardTests3

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests
open Mtg.Engine.FraRulingTests
open Mtg.Engine.FraCardTests
open Mtg.Engine.FraCardTests2

/-- Index of `o`'s activated ability whose printed line (or effect phrase)
mentions `needle`. -/
def abIdx (g : Game) (o : GameObject) (needle : String) : Nat :=
  let abs := g.activatedAbilitiesOf o
  ((List.range abs.size).find? (fun i =>
    mentions abs[i]!.printed needle || mentions abs[i]!.effect.phrase needle)).getD 0

/-- Index of `o`'s loyalty ability with symbol `sym`. -/
def loyIdx (g : Game) (o : GameObject) (sym : LoyaltySymbol) : Nat :=
  let abs := g.activatedAbilitiesOf o
  ((List.range abs.size).find? (fun i => abs[i]!.cost.loyalty == some sym)).getD 0

/-- Begin activating ability `idx` of object `id`: `steps` announce X and
targets, then mana is paid from a pool with every color. -/
def activateId (g : Game) (id : ObjectId) (idx : Nat) (steps : List Action := [])
    (p : PlayerId := me) : Game :=
  let g := everyColor g p 6
  let g := mustApply g p (.activate id idx)
  let g := steps.foldl (fun g a => mustApply g p a) g
  match g.pending with
  | .activateManaAbilities _ => mustApply g p .pay
  | _ => g

/-- Activate the ability of permanent `name` that mentions `needle`. -/
def activateNamed (g : Game) (name needle : String) (steps : List Action := [])
    (p : PlayerId := me) : Game :=
  let o := namedPermanent g name
  activateId g o.id (abIdx g o needle) steps p

/-- Activate the loyalty ability `sym` of planeswalker `name`. -/
def loyaltyAbility (g : Game) (name : String) (sym : LoyaltySymbol)
    (steps : List Action := []) : Game :=
  let o := namedPermanent g name
  activateId g o.id (loyIdx g o sym) steps

/-- True when activating `needle` of `o` is rejected. -/
def activationRejected (g : Game) (o : GameObject) (needle : String)
    (steps : List Action := []) (p : PlayerId := me) : Bool :=
  let g := everyColor g p 6
  match (g.apply p (.activate o.id (abIdx g o needle))).bind fun g =>
      steps.foldlM (fun g a => g.apply p a) g with
  | .error _ => true
  | .ok _ => false

def withLoyalty (g : Game) (name : String) (n : Nat) : Game :=
  g.mapObjectStatus (namedPermanent g name) (fun s => { s with loyaltyCounters := n })

def pw (card : CardDef) (n : Nat) (g : Game := afterDraw) : Game :=
  withLoyalty (addPermanent g card me me) card.name n

def loyaltyOf (g : Game) (name : String) : Nat := (namedPermanent g name).status.loyaltyCounters

def graveyardObj (g : Game) (p : PlayerId) (name : String) : GameObject := graveyardCard g p name

def handObj (g : Game) (p : PlayerId) (name : String) : GameObject := handCardNamed g p name

def power (g : Game) (name : String) : Int := g.power (namedPermanent g name)

def toughness (g : Game) (name : String) : Int := g.toughness (namedPermanent g name)

def kw (g : Game) (name : String) : Keywords := g.currentKeywords (namedPermanent g name)

def millN (g : Game) (p : PlayerId) (n : Nat) : Game :=
  (List.range n).foldl (fun g _ => addToGraveyard g island p) g

def onlyAbilitiesParsed (c : CardDef) : Bool := !keepsPrintedText c

/-! ## Every FRA card is fully parsed -/

#guard realityFractureCards.all onlyAbilitiesParsed

/-! ## Emrakul, the Exigent Doom (rulings 729 / 730) -/

/-- Emrakul exiled from hand by its ability, granting the Forest
“{T}: Add {C}{C}”. -/
def emrakulExiled : Game :=
  let g := addPermanent afterDraw forest me me
  let g := addToHand g emrakulTheExigentDoom me
  let card := handObj g me "Emrakul, the Exigent Doom"
  let o := namedPermanent g "Forest"
  resolved (activateId g card.id (abIdx g card "Exile this card") [.target (.permanent o.id)])

#guard inExile emrakulExiled "Emrakul, the Exigent Doom"
#guard (emrakulExiled.manaAbilitiesOf (namedPermanent emrakulExiled "Forest")).contains .colorless
#guard
  let g := emrakulExiled
  let g := mustApply g me (.tapForMana (namedPermanent g "Forest").id .colorless)
  (g.player me).manaPool.colorless == 2

/- Ruling 729: the land's ability can help pay for Emrakul cast from exile;
the ability ends once Emrakul is cast. -/
#guard (fraRuling 729).comment.contains "while casting Emrakul from exile"
#guard
  let g := { emrakulExiled with players := emrakulExiled.players.map (fun pl =>
    { pl with manaPool := {} }) }
  let card := (g.objects.find? (fun o => o.zone == .exile && o.name == "Emrakul, the Exigent Doom")).get!
  let g := withMana g me .black 8
  let g := mustApply g me (.cast card.id)
  let g := mustApply g me (.tapForMana (namedPermanent g "Forest").id .colorless)
  let g := mustApply g me .pay
  g.stack.any (fun e => (g.object! e.objectId).name == "Emrakul, the Exigent Doom") &&
    (namedPermanent g "Forest").status.colorlessGrantUntilCast.isEmpty

/- Ruling 730: if Emrakul leaves exile without being cast, the land keeps
the ability. -/
#guard (fraRuling 730).comment.contains "continue to have this ability"
#guard
  let g := emrakulExiled
  let card := (g.objects.find? (fun o => o.zone == .exile && o.name == "Emrakul, the Exigent Doom")).get!
  let (g, _) := g.move card.id (.graveyard me) none
  (g.manaAbilitiesOf (namedPermanent g "Forest")).contains .colorless &&
    ((mustApply g me (.tapForMana (namedPermanent g "Forest").id .colorless)).player me).manaPool.colorless == 2

/- Ward—Sacrifice three permanents: the opponent's spell is countered unless
they sacrifice three permanents. -/
#guard
  let g := addPermanent afterDraw emrakulTheExigentDoom me me
  let g := mustApply g me .pass
  let g := castFra g shock [tgt g "Emrakul, the Exigent Doom"] opp
  match g.pending with
  | .payWard q _ (.sacrificePermanents 3 0) => q == opp
  | _ => false
#guard
  let g := addPermanent afterDraw emrakulTheExigentDoom me me
  let g := [forest, forest, forest].foldl (fun g c => addPermanent g c opp opp) g
  let g := mustApply g me .pass
  let g := castFra g shock [tgt g "Emrakul, the Exigent Doom"] opp
  let lands := ((g.permanentsOf opp).filter (·.name == "Forest")).map (·.id)
  let g := lands.foldl (fun g id => mustApply g opp (.sacrifice id)) g
  let g := resolved g
  (g.permanentsOf opp).isEmpty && (namedPermanent g "Emrakul, the Exigent Doom").status.damage == 2

/-! ## White -/

/- Shatterwing Pegasus pumps your team. -/
#guard
  let g := addPermanent (addPermanent afterDraw shatterwingPegasus me me) grizzlyBears me me
  let g := resolved (activateNamed g "Shatterwing Pegasus" "Creatures you control")
  power g "Grizzly Bears" == 3 && toughness g "Shatterwing Pegasus" == 4

/- Gideon's Memorial: creature tokens get +1/+0 and vigilance; its mana can
only cast planeswalker spells. -/
#guard
  let g := addPermanent afterDraw gideonsMemorial me me
  let g := resolved (castFra g hexhavenBattalion)
  let cadet := namedPermanent g "Cadet"
  g.power cadet == 3 && (g.currentKeywords cadet).vigilance
#guard
  let g := addPermanent afterDraw gideonsMemorial me me
  let g := mustApply g me (.tapForMana (namedPermanent g "Gideon's Memorial").id (.colored .red))
  let g := addToHand g shock me
  let g := mustApply g me (.cast (handObj g me "Shock").id)
  let g := mustApply g me (.target (.player opp))
  let g := mustApply g me .pay
  g.stack.isEmpty && (g.player me).manaPool.fraRestricted.size == 1
#guard
  let g := addPermanent afterDraw gideonsMemorial me me
  let g := mustApply g me (.tapForMana (namedPermanent g "Gideon's Memorial").id (.colored .blue))
  let g := withMana g me .blue 1
  let g := withMana g me .black 3
  let g := addToHand g jaceRealitySculptor me
  let g := mustApply g me (.cast (handObj g me "Jace, Reality Sculptor").id)
  let g := mustApply g me .pay
  (g.player me).manaPool.fraRestricted.isEmpty && !g.stack.isEmpty

/- Liliana the Faultless gives another creature you control hexproof. -/
#guard
  let g := addPermanent (addPermanent afterDraw lilianaTheFaultless me me) grizzlyBears me me
  let before := (g.player me).graveyard.size
  let g := resolved (activateNamed g "Liliana the Faultless" "hexproof" [tgt g "Grizzly Bears"])
  (kw g "Grizzly Bears").hexproof && (g.player me).graveyard.size == before + 1

/- Rescue Girl returns another permanent you control, only during your turn. -/
#guard
  let g := addPermanent (addPermanent afterDraw rescueGirlFirstResponder me me) grizzlyBears me me
  let g := resolved (activateNamed g "Rescue Girl, First Responder" "Return" [tgt g "Grizzly Bears"])
  inHand g me "Grizzly Bears"
#guard
  let g := addPermanent afterDraw rescueGirlFirstResponder opp opp
  let g := addPermanent g grizzlyBears opp opp
  let g := mustApply g me .pass
  activationRejected g (namedPermanent g "Rescue Girl, First Responder") "Return"
    [tgt g "Grizzly Bears"] opp

/- Tomik, Orzhov Lawmage gives a creature with a +1/+1 counter flying. -/
#guard
  let g := addPermanent (addPermanent afterDraw tomikOrzhovLawmage me me) grizzlyBears me me
  let g := plusOnes g "Grizzly Bears" 1
  let g := resolved (activateNamed g "Tomik, Orzhov Lawmage" "flying" [tgt g "Grizzly Bears"])
  (kw g "Grizzly Bears").flying

/- Yoshimaru, Beloved Companion: one more +1/+1 counter is put on your
creatures; {6} puts a counter on a legendary creature. -/
#guard
  let g := addPermanent (addPermanent afterDraw yoshimaruBelovedCompanion me me) grizzlyBears me me
  let g := resolved (castFra g predictivePreparations
    [.targets #[perm g "Grizzly Bears", perm g "Yoshimaru, Beloved Companion"]])
  counters g "Grizzly Bears" == 2 && counters g "Yoshimaru, Beloved Companion" == 2
#guard
  let g := addPermanent afterDraw yoshimaruBelovedCompanion me me
  let g := resolved (activateNamed g "Yoshimaru, Beloved Companion" "legendary"
    [tgt g "Yoshimaru, Beloved Companion"])
  counters g "Yoshimaru, Beloved Companion" == 2

/- Thalia, the Survivor: the opponent's noncreature spells cost {1} more. -/
#guard
  let g := addPermanent afterDraw thaliaTheSurvivor me me
  let shockCard := (insertObject g shock opp (.hand opp)).objects.back!
  (g.playManaCost { shockCard with controller := some opp } shock).manaValue == 2 &&
    (g.playManaCost { shockCard with owner := me, controller := some me } shock).manaValue == 1

/- Yuriko, Blade of the Mighty: no spells or non-mana abilities in combat. -/
#guard
  let g := addPermanent afterDraw yurikoBladeOfTheMighty me me
  let g := addPermanent g shatterwingPegasus me me
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := skipToPending g .declareAttackers 80
  let g := mustApply g me (.declareAttackers #[])
  g.combatLocksNonManaAbilities &&
    !(addToHand g shock me |> fun g => g.canCast me (handObj g me "Shock")) &&
    activationRejected g (namedPermanent g "Shatterwing Pegasus") "Creatures you control"

/- Ajani Resolute's ultimate emblem gives your creatures +2/+2. -/
#guard
  let g := addPermanent (pw ajaniResolute 10) grizzlyBears me me
  let g := resolved (loyaltyAbility g "Ajani Resolute" (.minus 10))
  power g "Grizzly Bears" == 4 && toughness g "Grizzly Bears" == 4 &&
    g.objects.any (fun o => o.zone == .command && o.controlledBy me)

/-! ## Blue -/

/- The Theorist, Jace Beleren: +1 makes an Illusion; −2 returns up to one
artifact or creature each opponent controls; −6 draws three, then puts a
+1/+1 counter on each creature you control per card in hand. -/
#guard
  let g := resolved (loyaltyAbility (pw theTheoristJaceBeleren 3) "The Theorist, Jace Beleren" (.plus 1))
  g.battlefield.any (fun o => o.printed.isToken && g.hasSubtype o "Illusion") &&
    loyaltyOf g "The Theorist, Jace Beleren" == 4
#guard
  let g := pw theTheoristJaceBeleren 3 withBears
  let g := resolved (loyaltyAbility g "The Theorist, Jace Beleren" (.minus 2) [tgt g "Grizzly Bears"])
  inHand g opp "Grizzly Bears"
#guard
  let g := addPermanent (pw theTheoristJaceBeleren 6) grizzlyBears me me
  let g := resolved (loyaltyAbility g "The Theorist, Jace Beleren" (.minus 6))
  counters g "Grizzly Bears" == handSize g me && handSize g me ≥ 3

/- Theorist's Proxy: the next spell you cast this turn can't be countered. -/
#guard
  let g := addPermanent afterDraw theoristsProxy me me
  let g := resolved (activateNamed g "Theorist's Proxy" "can't be countered")
  let g := castFra g shock [.target (.player opp)]
  !onBattlefield g "Theorist's Proxy" &&
    g.stack.any (fun e => (g.object! e.objectId).uncounterableThisCast)

/- Undulating Witness trades a toughness for a power. -/
#guard
  let g := addPermanent afterDraw undulatingWitness me me
  let g := resolved (activateNamed g "Undulating Witness" "+1/-1")
  power g "Undulating Witness" == 4 && toughness g "Undulating Witness" == 4

/- Seasoned Cryomancer exiles itself from your graveyard to draw two. -/
#guard
  let g := addToGraveyard afterDraw seasonedCryomancer me
  let before := handSize g me
  let card := graveyardObj g me "Seasoned Cryomancer"
  let g := resolved (activateId g card.id (abIdx g card "Draw two"))
  handSize g me == before + 2 && inExile g "Seasoned Cryomancer"

/- Surveillance Phantasm surveils, then can attack despite defender. -/
#guard
  let g := addPermanent afterDraw surveillancePhantasm me me
  let before := !g.canAttack (namedPermanent g "Surveillance Phantasm")
  let g := activateNamed g "Surveillance Phantasm" "Surveil"
  let g := resolved g
  before && (g.player me).scriedOrSurveilledThisTurn &&
    g.canAttack (namedPermanent g "Surveillance Phantasm")

/- Paradox Shaper puts a card from your graveyard on the bottom of your
library. -/
#guard
  let g := addToGraveyard (addPermanent afterDraw paradoxShaper me me) shock me
  let g := resolved (activateNamed g "Paradox Shaper" "bottom" [gyTarget g me "Shock"])
  ((g.player me).library[0]?.map (fun id => (g.object! id).name)) == some "Shock"

/- Hapatra, the Desert Frost untaps a creature. -/
#guard
  let g := tapped (addPermanent (addPermanent afterDraw hapatraTheDesertFrost me me) grizzlyBears me me)
    "Grizzly Bears"
  let g := resolved (activateNamed g "Hapatra, the Desert Frost" "Untap" [tgt g "Grizzly Bears"])
  !(namedPermanent g "Grizzly Bears").status.tapped

/- Arni, Humble Scribe loots. -/
#guard
  let g := addPermanent afterDraw arniHumbleScribe me me
  let before := (handSize g me, (g.player me).graveyard.size)
  let g := resolved (activateNamed g "Arni, Humble Scribe" "Draw")
  (handSize g me, (g.player me).graveyard.size) == (before.1, before.2 + 1)

/- Chandra, Chill of Compliance. -/
#guard
  let g := addToLibraryTop (pw chandraChillOfCompliance 3) shock me
  let g := loyaltyAbility g "Chandra, Chill of Compliance" (.plus 1)
  let g := resolveTop g
  let shockId := (g.player me).library.back!
  let g := mustApply g me (.surveil #[] #[shockId])
  inHand g me "Shock" && loyaltyOf g "Chandra, Chill of Compliance" == 4
#guard
  let g := pw chandraChillOfCompliance 3
  let o := namedPermanent g "Chandra, Chill of Compliance"
  let g := resolved (activateId g o.id (abIdx g o "Add"))
  (g.player me).manaPool.fraRestricted.contains (.colored .blue, .noncreatureSpell)
#guard
  let g := pw chandraChillOfCompliance 3 withBears
  let g := resolved (loyaltyAbility g "Chandra, Chill of Compliance" .minusX
    [.chooseX 2, tgt g "Grizzly Bears"])
  let bears := namedPermanent g "Grizzly Bears"
  bears.status.tapped && bears.status.stun == 2 && loyaltyOf g "Chandra, Chill of Compliance" == 1
#guard
  let g := pw chandraChillOfCompliance 3
  let o := namedPermanent g "Chandra, Chill of Compliance"
  activationRejected g o "Tap target" [.chooseX 4]
#guard
  let g := resolved (loyaltyAbility (pw chandraChillOfCompliance 6) "Chandra, Chill of Compliance" (.minus 6))
  let before := handSize g me
  let g := resolved (castFra g shock [.target (.player opp)])
  handSize g me == before + 1

/- Jace, Reality Sculptor: +1 empowers Jace by your Islands; 0 needs
twenty-five loyalty among your Jaces. -/
#guard
  let g := addPermanent (addPermanent (pw jaceRealitySculptor 5) island me me) island me me
  let g := resolved (loyaltyAbility g "Jace, Reality Sculptor" (.plus 1))
  (jaceTokenOf g).status.loyaltyCounters == 2
#guard
  let g := pw jaceRealitySculptor 5
  activationRejected g (namedPermanent g "Jace, Reality Sculptor") "Exile all but"
#guard
  let g := pw jaceRealitySculptor 25
  let o := namedPermanent g "Jace, Reality Sculptor"
  let g := resolved (activateId g o.id (loyIdx g o .zero))
  (g.player opp).library.size == 1

/- Jace's −3: until your next turn, a creature attacking you or your
planeswalker gets minus five power. -/
def jaceMinusThree : Game :=
  let g := addPermanent (pw jaceRealitySculptor 5) grizzlyBears opp opp
  resolved (loyaltyAbility g "Jace, Reality Sculptor" (.minus 3))

def oppDeclares (g : Game) : Game :=
  let g := skipToPending g .declareAttackers 200
  let g := if g.activePlayer == me then skipToPending (applyIdle g) .declareAttackers 200 else g
  g

#guard
  let g := oppDeclares jaceMinusThree
  let g := mustApply g opp (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])
  let g := settle g
  g.activePlayer == opp && power g "Grizzly Bears" == -3
#guard
  let g := oppDeclares jaceMinusThree
  let g := mustApply g opp (.declareAttackers #[(namedPermanent g "Grizzly Bears").id] none #[]
    #[some (namedPermanent g "Jace, Reality Sculptor").id])
  let g := settle g
  power g "Grizzly Bears" == -3

/- Lyra, Tolarian Archangel: until end of turn, combat damage to a player
draws two cards. -/
#guard
  let g := addPermanent afterDraw lyraTolarianArchangel me me
  let g := resolved (activateNamed g "Lyra, Tolarian Archangel" "combat damage")
  let before := handSize g me
  let g := attackThen g #["Lyra, Tolarian Archangel"]
  handSize g me == before + 2 && life g opp == 17

/-! ## Black -/

/- Theoretical Necromancer returns another creature card from your
graveyard. -/
#guard
  let g := addToGraveyard (addToGraveyard afterDraw theoreticalNecromancer me) grizzlyBears me
  let card := graveyardObj g me "Theoretical Necromancer"
  let g := resolved (activateId g card.id (abIdx g card "Return") [gyTarget g me "Grizzly Bears"])
  inHand g me "Grizzly Bears" && inExile g "Theoretical Necromancer"

/- Blessed Ghoul returns to your hand from your graveyard. -/
#guard
  let g := addToGraveyard afterDraw blessedGhoul me
  let card := graveyardObj g me "Blessed Ghoul"
  inHand (resolved (activateId g card.id (abIdx g card "Return"))) me "Blessed Ghoul"

/- Gallia, Tragic Host returns tapped with a counter, exiling another
creature card. -/
#guard
  let g := addToGraveyard (addToGraveyard afterDraw galliaTragicHost me) grizzlyBears me
  let card := graveyardObj g me "Gallia, Tragic Host"
  let g := resolved (activateId g card.id (abIdx g card "Return"))
  let gallia := namedPermanent g "Gallia, Tragic Host"
  gallia.status.tapped && gallia.status.plusOnePlusOne == 1 && inExile g "Grizzly Bears"
#guard
  let g := addToGraveyard afterDraw galliaTragicHost me
  activationRejected g (graveyardObj g me "Gallia, Tragic Host") "Return"

/- Proft, Sinister Mastermind: discard it to shrink a creature until end of turn. -/
#guard
  let g := addToHand withGiant proftSinisterMastermind me
  let card := handObj g me "Proft, Sinister Mastermind"
  let g := resolved (activateId g card.id (abIdx g card "Target creature") [tgt g "Hill Giant"])
  power g "Hill Giant" == 0 && toughness g "Hill Giant" == 2 && inGraveyard g me "Proft, Sinister Mastermind"

/- Garruk, Veiled Butcher. -/
#guard
  let g := pw garrukVeiledButcher 5 withGiant
  let g := resolved (loyaltyAbility g "Garruk, Veiled Butcher" (.plus 2) [tgt g "Hill Giant"])
  power g "Hill Giant" == -1 && toughness g "Hill Giant" == 2 &&
    loyaltyOf g "Garruk, Veiled Butcher" == 7
/- The reduction lasts through the opponent's turn and ends as your next turn
begins. -/
#guard
  let g := pw garrukVeiledButcher 5 withGiant
  let g := resolved (loyaltyAbility g "Garruk, Veiled Butcher" (.plus 2) [tgt g "Hill Giant"])
  let g := oppDeclares g
  let during := power g "Hill Giant" == -1
  let g := skipTo (applyIdle g) .upkeep 300
  during && g.activePlayer == me && power g "Hill Giant" == 3
/- −2: each player sacrifices a creature; you made a Beast. An opponent's
creature is exiled instead of dying. -/
#guard
  let g := addPermanent (pw garrukVeiledButcher 5 withGiant) grizzlyBears me me
  let g := settle (loyaltyAbility g "Garruk, Veiled Butcher" (.minus 2))
  !onBattlefield g "Grizzly Bears" && inExile g "Hill Giant" && creaturesNamed g "Beast" == 1
/- −3: the opponent discards two cards; you draw for each opponent who
didn't discard two nonland cards. -/
#guard
  let g0 := pw garrukVeiledButcher 5
  let g := g0.modifyPlayer opp (fun pl => { pl with hand := #[] })
  let g := addToHand (addToHand (addToHand g forest opp) forest opp) shock opp
  let before := handSize g me
  let g := settle (loyaltyAbility g "Garruk, Veiled Butcher" (.minus 3))
  handSize g opp == 1 && handSize g me == before + 1

/- Edgar, Ancient Bloodlord sacrifices another creature for a counter and
menace. -/
#guard
  let g := addPermanent (addPermanent afterDraw edgarAncientBloodlord me me) grizzlyBears me me
  let g := resolved (activateNamed g "Edgar, Ancient Bloodlord" "menace")
  counters g "Edgar, Ancient Bloodlord" == 1 && g.hasMenace (namedPermanent g "Edgar, Ancient Bloodlord") &&
    !onBattlefield g "Grizzly Bears"

/-! ## Red -/

/- Identity Echo exiles your creature and reveals until a creature card,
putting the rest on the bottom. -/
#guard
  let g := addPermanent (addPermanent afterDraw identityEcho me me) grizzlyBears me me
  let g := addToLibraryTop (addToLibraryTop g hillGiant me) island me
  let g := resolved (activateNamed g "Identity Echo" "Exile target" [tgt g "Grizzly Bears"])
  inExile g "Grizzly Bears" && onBattlefield g "Hill Giant" &&
    ((g.player me).library[0]?.map (fun id => (g.object! id).name)) == some "Island"

/- Hallway Heckler: tap and discard a card to draw a card. -/
#guard
  let g := addPermanent afterDraw hallwayHeckler me me
  let before := (handSize g me, (g.player me).graveyard.size)
  let g := resolved (activateNamed g "Hallway Heckler" "Draw a card")
  (handSize g me, (g.player me).graveyard.size) == (before.1, before.2 + 1)

/- Ingris Stingerquill makes a Cadet, then your creatures gain haste. -/
#guard
  let g := addPermanent afterDraw ingrisStingerquill me me
  let g := resolved (activateNamed g "Ingris Stingerquill" "Cadet")
  (kw g "Cadet").haste && (kw g "Ingris Stingerquill").haste

/- Pia, Determined Rebuilder pumps by the number of artifacts you control. -/
#guard
  let g := addPermanent (addPermanent afterDraw piaDeterminedRebuilder me me) murmuringVolume me me
  let g := addPermanent g theEchoverseFulcrum me me
  let g := resolved (activateNamed g "Pia, Determined Rebuilder" "+X/+0" [tgt g "Pia, Determined Rebuilder"])
  power g "Pia, Determined Rebuilder" == 4

/- Kiora of Fire and Ashes makes a Dragon. -/
#guard
  let g := addPermanent afterDraw kioraOfFireAndAshes me me
  let g := resolved (activateNamed g "Kiora of Fire and Ashes" "Dragon")
  creaturesNamed g "Dragon" == 1

/- Marwyn, the Clearcutter sacrifices an artifact or land to draw. -/
#guard
  let g := addPermanent (addPermanent afterDraw marwynTheClearcutter me me) murmuringVolume me me
  let before := handSize g me
  let g := resolved (activateNamed g "Marwyn, the Clearcutter" "Draw")
  handSize g me == before + 1 && !onBattlefield g "Murmuring Volume"

/- Skilled Battlecarver has first strike only during your turn. -/
#guard
  let g := addPermanent afterDraw skilledBattlecarver me me
  (kw g "Skilled Battlecarver").firstStrike &&
    !(kw (addPermanent afterDraw skilledBattlecarver opp opp) "Skilled Battlecarver").firstStrike

/- Ajani's Anguish gives your creatures trample. -/
#guard (kw (addPermanent (addPermanent afterDraw ajanisAnguish me me) grizzlyBears me me) "Grizzly Bears").trample

/- Gallia, the Merrymaker gives other creatures with +1/+1 counters haste. -/
#guard
  let g := addPermanent (addPermanent afterDraw galliaTheMerrymaker me me) grizzlyBears me me
  !(kw g "Grizzly Bears").haste && (kw (plusOnes g "Grizzly Bears" 1) "Grizzly Bears").haste

/- Samut, Hazoret's Champion gives your creatures haste, so a summoning-sick
creature can attack. -/
#guard
  let g := addPermanent afterDraw samutHazoretsChampion me me
  let g := enterPermanent g grizzlyBears me
  let g := g.mapObjectStatus (namedPermanent g "Grizzly Bears") (fun s => { s with summoningSick := true })
  g.canAttack (namedPermanent g "Grizzly Bears")

/- Tomik, Izzet Sparkmage: noncombat damage to an opponent or their
permanent is increased by 1. -/
#guard
  let g := addPermanent withGiant tomikIzzetSparkmage me me
  let g := resolved (castFra g shock [.target (.player opp)])
  let g := resolved (castFra g shock [tgt g "Hill Giant"])
  life g opp == 17 && !onBattlefield g "Hill Giant"

/- Thopters you control have haste (Saheeli, Jewel of Avishkar). -/
#guard
  let g := addPermanent afterDraw saheeliJewelOfAvishkar me me
  let g := resolved (castFra g shock [.target (.player opp)])
  (kw g "Thopter").haste

/- Whiplash Wordsmith has flying and haste once an opponent was dealt
noncombat damage this turn. -/
#guard
  let g := addPermanent afterDraw whiplashWordsmith me me
  let before := (kw g "Whiplash Wordsmith").flying
  let g := resolved (castFra g shock [.target (.player opp)])
  !before && (kw g "Whiplash Wordsmith").flying && (kw g "Whiplash Wordsmith").haste

/- Ajani Unrelenting: −2 discards your hand and draws per creature; −3 deals
4 damage to each creature except your tokens. -/
#guard
  let g := addPermanent (addPermanent (pw ajaniUnrelenting 5) grizzlyBears me me) hillGiant me me
  let g := settle (loyaltyAbility g "Ajani Unrelenting" (.minus 2))
  handSize g me == 3
#guard
  let g := addPermanent (pw ajaniUnrelenting 5 withGiant) grizzlyBears me me
  let g := settle (loyaltyAbility g "Ajani Unrelenting" (.minus 3))
  !onBattlefield g "Hill Giant" && !onBattlefield g "Grizzly Bears" && onBattlefield g "Cadet"

/-! ## Green -/

/- Budding Insurgent destroys an artifact or enchantment and draws if it was
a legendary enchantment. -/
#guard
  let g := addPermanent (addPermanent afterDraw buddingInsurgent me me) wayOfTheParadox opp opp
  let before := handSize g me
  let g := resolved (activateNamed g "Budding Insurgent" "Destroy" [tgt g "Way of the Paradox"])
  !onBattlefield g "Way of the Paradox" && handSize g me == before + 1
#guard
  let g := addPermanent (addPermanent afterDraw buddingInsurgent me me) murmuringVolume opp opp
  let before := handSize g me
  let g := resolved (activateNamed g "Budding Insurgent" "Destroy" [tgt g "Murmuring Volume"])
  !onBattlefield g "Murmuring Volume" && handSize g me == before

/- Hungering Puppetbeast sacrifices another artifact for a counter and your
choice of trample, hexproof, or haste. -/
#guard
  let g := addPermanent (addPermanent afterDraw hungeringPuppetbeast me me) murmuringVolume me me
  let g := resolveTop (activateNamed g "Hungering Puppetbeast" "+1/+1 counter")
  let g := mustApply g me (.chooseMode 2)
  counters g "Hungering Puppetbeast" == 1 && (kw g "Hungering Puppetbeast").haste &&
    !onBattlefield g "Murmuring Volume"

/- Puppet Crafting enchants an artifact and makes it a 5/5 Construct
creature; it can't enchant a creature that isn't an artifact. -/
#guard
  let g := addPermanent afterDraw murmuringVolume me me
  let g := resolved (castFra g puppetCrafting [tgt g "Murmuring Volume"])
  let v := namedPermanent g "Murmuring Volume"
  v.isCreature && g.power v == 5 && g.toughness v == 5 && g.hasSubtype v "Construct"
#guard castRejected withBears puppetCrafting [tgt withBears "Grizzly Bears"]
#guard
  let g := addToGraveyard afterDraw puppetCrafting me
  let card := graveyardObj g me "Puppet Crafting"
  inHand (resolved (activateId g card.id (abIdx g card "Return"))) me "Puppet Crafting"

/- Sureshot Sower is discarded to destroy a creature with flying. -/
#guard
  let g := addPermanent afterDraw shatterwingPegasus opp opp
  let g := addToHand g sureshotSower me
  let card := handObj g me "Sureshot Sower"
  let g := resolved (activateId g card.id (abIdx g card "Destroy") [tgt g "Shatterwing Pegasus"])
  !onBattlefield g "Shatterwing Pegasus" && inGraveyard g me "Sureshot Sower"

/- Wrecking Gecko gets +4/+4 and trample. -/
#guard
  let g := addPermanent afterDraw wreckingGecko me me
  let g := resolved (activateNamed g "Wrecking Gecko" "+4/+4")
  power g "Wrecking Gecko" == 9 && (kw g "Wrecking Gecko").trample

/- Edgar, Moonlit Sovereign adds a counter to each creature that has one. -/
#guard
  let g := addPermanent (addPermanent afterDraw edgarMoonlitSovereign me me) grizzlyBears me me
  let g := plusOnes g "Grizzly Bears" 1
  let g := resolved (activateNamed g "Edgar, Moonlit Sovereign" "each creature")
  counters g "Grizzly Bears" == 2 && counters g "Edgar, Moonlit Sovereign" == 0

/- Marwyn, the Preserver: lands you control have hexproof; {2} returns a land
card from your graveyard. -/
#guard
  let g := addPermanent (addPermanent afterDraw marwynThePreserver me me) forest me me
  (kw g "Forest").hexproof && !g.canBeTargetedBy opp (namedPermanent g "Forest")
#guard
  let g := addToGraveyard (addPermanent afterDraw marwynThePreserver me me) forest me
  inHand (resolved (activateNamed g "Marwyn, the Preserver" "land card" [gyTarget g me "Forest"])) me "Forest"

/- Garruk, Curse Breaker: +2 untaps up to two lands; −4 pumps creatures
attacking your opponents until your next turn. -/
#guard
  let g := addPermanent (addPermanent (pw garrukCurseBreaker 5) forest me me) island me me
  let g := tapped (tapped g "Forest") "Island"
  let g := resolved (loyaltyAbility g "Garruk, Curse Breaker" (.plus 2)
    [.targets #[perm g "Forest", perm g "Island"]])
  !(namedPermanent g "Forest").status.tapped && !(namedPermanent g "Island").status.tapped
#guard
  let g := addPermanent (pw garrukCurseBreaker 5) grizzlyBears me me
  let g := resolved (loyaltyAbility g "Garruk, Curse Breaker" (.minus 4))
  let g := attackThen g #["Grizzly Bears"]
  life g opp == 16

/- Dark Matter Manipulator gets +2/+0 for every seven cards in your
graveyard. -/
#guard power (addPermanent (millN afterDraw me 14) darkMatterManipulator me me) "Dark Matter Manipulator" == 5

/- Theorix Metamage gets +1/+0 and flying with seven cards in your
graveyard. -/
#guard
  let g := addPermanent (millN afterDraw me 7) theorixMetamage me me
  power g "Theorix Metamage" == 3 && (kw g "Theorix Metamage").flying

/- Mind Meanderer has vigilance while you control a Jace planeswalker. -/
#guard
  let g := addPermanent afterDraw mindMeanderer me me
  !(kw g "Mind Meanderer").vigilance && (kw (pw jaceRealitySculptor 5 g) "Mind Meanderer").vigilance

/- Vigorbloom Vanguard: creatures you control with +1/+1 counters have
vigilance. -/
#guard
  let g := addPermanent (addPermanent afterDraw vigorbloomVanguard me me) grizzlyBears me me
  (kw (plusOnes g "Grizzly Bears" 1) "Grizzly Bears").vigilance && !(kw g "Grizzly Bears").vigilance

/- Ghalta the Unstoppable gives other creatures you control trample. -/
#guard (kw (addPermanent (addPermanent afterDraw ghaltaTheUnstoppable me me) grizzlyBears me me) "Grizzly Bears").trample

/- Fblthp, Knows the Way: power equal to basic land types among your lands. -/
#guard
  let g := addPermanent (addPermanent (addPermanent afterDraw fblthpKnowsTheWay me me) forest me me) island me me
  let g := addPermanent g forest me me
  power g "Fblthp, Knows the Way" == 2

/- Ruric Thar, Magecrusher has hexproof until they deal combat damage. -/
#guard
  let g := addPermanent afterDraw ruricTharMagecrusher me me
  let before := (kw g "Ruric Thar, Magecrusher").hexproof
  let g := attackThen g #["Ruric Thar, Magecrusher"]
  before && !(kw g "Ruric Thar, Magecrusher").hexproof && life g opp == 13

/-! ## Multicolor and colorless -/

/- Shatterwing-style pumps aside, Bloombrute grants trample and lifelink. -/
#guard
  let g := addPermanent (addPermanent afterDraw bloombrute me me) grizzlyBears me me
  let g := resolved (activateNamed g "Bloombrute" "trample and lifelink" [tgt g "Grizzly Bears"])
  (kw g "Grizzly Bears").trample && (kw g "Grizzly Bears").lifelink

/- Aerid Konstrari makes a Heartwood, then gets +X/+0 per artifact. -/
#guard
  let g := addPermanent afterDraw aeridKonstrari me me
  let g := resolved (activateNamed g "Aerid Konstrari" "Heartwood")
  power g "Aerid Konstrari" == 6

/- Proctor of Potential returns from your graveyard with a finality counter
only if you've scried or surveilled this turn. -/
#guard
  let g := addToGraveyard afterDraw proctorOfPotential me
  activationRejected g (graveyardObj g me "Proctor of Potential") "Return"
#guard
  let g := addToGraveyard afterDraw proctorOfPotential me
  let g := g.modifyPlayer me (fun pl => { pl with scriedOrSurveilledThisTurn := true })
  let card := graveyardObj g me "Proctor of Potential"
  let g := resolved (activateId g card.id (abIdx g card "Return"))
  (namedPermanent g "Proctor of Potential").status.finality == 1

/- Solitary Cell discards a legendary card to draw. -/
#guard
  let g := addToHand (addPermanent afterDraw solitaryCell me me) ruricTharMagecrusher me
  let before := handSize g me
  let g := resolved (activateNamed g "Solitary Cell" "Draw")
  handSize g me == before && inGraveyard g me "Ruric Thar, Magecrusher"

/- Tenured Tethermage taps two untapped artifacts for two counters. -/
#guard
  let g := addPermanent afterDraw tenuredTethermage me me
  let g := addPermanent (addPermanent g murmuringVolume me me) murmuringVolume me me
  let g := resolved (activateNamed g "Tenured Tethermage" "two +1/+1")
  counters g "Tenured Tethermage" == 2 &&
    ((g.permanentsOf me).filter (fun o => o.name == "Murmuring Volume" && o.status.tapped)).size == 2

/- Warrior's Blades: equip costs {1} less for each +1/+1 counter on the
target. -/
#guard
  let g := addPermanent (addPermanent afterDraw warriorsBlades me me) grizzlyBears me me
  let g := plusOnes g "Grizzly Bears" 2
  let g := withMana g me .red 1
  let blades := namedPermanent g "Warrior's Blades"
  let g := mustApply g me (.activate blades.id (abIdx g blades "Equip"))
  let g := mustApply g me (tgt g "Grizzly Bears")
  let g := resolved (mustApply g me .pay)
  (namedPermanent g "Warrior's Blades").attachedTo == some (namedPermanent g "Grizzly Bears").id

/- Afterthought Sentry gains flying. -/
#guard
  let g := addPermanent afterDraw afterthoughtSentry me me
  (kw (resolved (activateNamed g "Afterthought Sentry" "flying")) "Afterthought Sentry").flying

/- The Echoverse Fulcrum exiles itself to destroy all creatures. -/
#guard
  let g := addPermanent (addPermanent withBears theEchoverseFulcrum me me) grizzlyBears me me
  let g := resolved (activateNamed g "The Echoverse Fulcrum" "Destroy all")
  !onBattlefield g "Grizzly Bears" && inExile g "The Echoverse Fulcrum"

/- Living Library: the target's owner shuffles it into their library. -/
#guard
  let g := addPermanent withBears livingLibrary me me
  let before := (g.player opp).library.size
  let g := resolved (activateNamed g "Living Library" "shuffles" [tgt g "Grizzly Bears"])
  !onBattlefield g "Grizzly Bears" && (g.player opp).library.size == before + 1

/- Murmuring Volume: discard a card to draw. -/
#guard
  let g := addPermanent afterDraw murmuringVolume me me
  let before := (handSize g me, (g.player me).graveyard.size)
  let g := resolved (activateNamed g "Murmuring Volume" "Draw")
  (handSize g me, (g.player me).graveyard.size) == (before.1, before.2 + 1)

/- Heartwood Crafter's mana can't be spent to cast spells from your hand. -/
#guard
  let g := addPermanent afterDraw heartwoodCrafter me me
  let g := mustApply g me (.tapForMana (namedPermanent g "Heartwood Crafter").id .colorless)
  let pool := (g.player me).manaPool
  !pool.canPay (ManaCost.ofGeneric 1) (spend := { spell := true, fromHand := true }) &&
    pool.canPay (ManaCost.ofGeneric 1) (spend := { spell := true }) &&
    pool.canPay (ManaCost.ofGeneric 1)

/- Geist of Saint Thalia: your noncreature spells cost {1} less. Traxos,
Academy Guardian costs {2} less after you cast a noncreature spell. -/
#guard
  let g := addPermanent afterDraw geistOfSaintThalia me me
  let g := addToHand g murmuringVolume me
  (g.playManaCost (handObj g me "Murmuring Volume") murmuringVolume).manaValue == 2
#guard
  let g := addToHand afterDraw traxosAcademyGuardian me
  let before := (g.playManaCost (handObj g me "Traxos, Academy Guardian") traxosAcademyGuardian).manaValue
  let g := resolved (castFra g shock [.target (.player opp)])
  let after := (g.playManaCost (handObj g me "Traxos, Academy Guardian") traxosAcademyGuardian).manaValue
  before == 4 && after == 2

/- Vraska, Soul of Stone gives artifact creatures vigilance. -/
#guard (kw (addPermanent (addPermanent afterDraw vraskaSoulOfStone me me) livingLibrary me me) "Living Library").vigilance

/- Traxos, Scourge Eternal doesn't untap during your untap step. -/
#guard
  let g := tapped (addPermanent afterDraw traxosScourgeEternal me me) "Traxos, Scourge Eternal"
  let g := skipTo (skipTo g .end 300) .upkeep 300
  let g := skipTo (skipTo (applyIdle g) .end 300) .upkeep 300
  g.activePlayer == me && (namedPermanent g "Traxos, Scourge Eternal").status.tapped

/- Winter, Tormented Loner gets +1/+0 per creature and planeswalker card in
your graveyard. -/
#guard
  let g := addToGraveyard (addToGraveyard (addToGraveyard afterDraw grizzlyBears me) jaceRealitySculptor me) shock me
  power (addPermanent g winterTormentedLoner me me) "Winter, Tormented Loner" == 2

/- Creatures you control can attack despite defender (Ghalta the
Immovable). -/
#guard
  let g := addPermanent (addPermanent afterDraw ghaltaTheImmovable me me) surveillancePhantasm me me
  g.canAttack (namedPermanent g "Surveillance Phantasm")

/- Room of Refuge enters tapped and taps for its chosen color. -/
#guard
  let g := addToHand afterDraw roomOfRefuge me
  let g := mustApply g me (.playLand (handObj g me "Room of Refuge").id)
  let wasPending := (pendingFra g).isSome
  let g := mustApply g me (.chooseMode 3)
  let room := namedPermanent g "Room of Refuge"
  wasPending && room.status.tapped && room.status.chosenColor == some .red &&
    (g.manaAbilitiesOf room).contains (.colored .red)

/- Equipment and Auras: Hunter's Axe, Medic's Kitesail, Ferocity of the
Hunt. -/
def equip (g : Game) (gear host : String) : Game :=
  let o := namedPermanent g gear
  g.setObject { o with attachedTo := some (namedPermanent g host).id }

#guard
  let g := equip (addPermanent (addPermanent afterDraw huntersAxe me me) grizzlyBears me me) "Hunter's Axe" "Grizzly Bears"
  let g := attackThen g #["Grizzly Bears"]
  life g opp == 16
#guard
  let g := equip (addPermanent (addPermanent afterDraw huntersAxe me me) grizzlyBears me me) "Hunter's Axe" "Grizzly Bears"
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g me (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])
  let g := resolveTop (stackTriggers g)
  let g := mustApply g me (.chooseMode 1)
  (kw g "Grizzly Bears").deathtouch && power g "Grizzly Bears" == 4
#guard
  let g := equip (addPermanent (addPermanent afterDraw medicsKitesail me me) grizzlyBears me me) "Medic's Kitesail" "Grizzly Bears"
  let flying := (kw g "Grizzly Bears").flying
  let g := attackThen g #["Grizzly Bears"]
  flying && life g opp == 17 && life g me == 21
#guard
  let g := equip (addPermanent (addPermanent afterDraw ferocityOfTheHunt me me) grizzlyBears me me) "Ferocity of the Hunt" "Grizzly Bears"
  power g "Grizzly Bears" == 3 && g.hasDeathtouch (namedPermanent g "Grizzly Bears")

/-! ## Abilities granted to planeswalkers -/

/- Sanctum Lurker grants “[+2]: This planeswalker deals 1 damage to each
opponent and you gain 1 life.” -/
#guard
  let g := addPermanent (pw ajaniResolute 2) sanctumLurker me me
  let g := resolved (loyaltyAbility g "Ajani Resolute" (.plus 2))
  life g opp == 19 && life g me == 21 && loyaltyOf g "Ajani Resolute" == 5

/- Avatar of Burgeoning Echoes grants “[−10]: Put a +1/+1 counter on target
creature for each land you control.” -/
#guard
  let g := addPermanent (pw jaceRealitySculptor 10) avatarOfBurgeoningEchoes me me
  let g := addPermanent (addPermanent g forest me me) forest me me
  let g := resolved (loyaltyAbility g "Jace, Reality Sculptor" (.minus 10) [tgt g "Avatar of Burgeoning Echoes"])
  counters g "Avatar of Burgeoning Echoes" == 2

/- Way of the Deathbringer grants “[−2]: You may sacrifice a creature. If you
do, create a 4/4 Beast.” -/
#guard
  let g := addPermanent (addPermanent (pw ajaniUnrelenting 5) wayOfTheDeathbringer me me) grizzlyBears me me
  let o := namedPermanent g "Ajani Unrelenting"
  let idx := abIdx g o "You may sacrifice a creature"
  let g := resolveTop (stackTriggers (activateId g o.id idx))
  let g := resolveTop g
  let g := mustApply g me (.choosePermanents #[(namedPermanent g "Grizzly Bears").id])
  creaturesNamed g "Beast" == 1 && !onBattlefield g "Grizzly Bears"

/- Way of the Warlord grants “[−4]: deals 2 damage to up to one target
creature or planeswalker and 2 damage to target player.” -/
#guard
  let g := addPermanent (pw jaceRealitySculptor 4 withBears) wayOfTheWarlord me me
  let g := resolved (loyaltyAbility g "Jace, Reality Sculptor" (.minus 4)
    [tgt g "Grizzly Bears", .target (.player opp)])
  !onBattlefield g "Grizzly Bears" && life g opp == 18

/- Kiora of Salt and Sand grants “[−8]: Create an 8/8 Leviathan with
hexproof.” -/
#guard
  let g := addPermanent (pw jaceRealitySculptor 8) kioraOfSaltAndSand me me
  let g := resolved (loyaltyAbility g "Jace, Reality Sculptor" (.minus 8))
  (kw g "Leviathan").hexproof && power g "Leviathan" == 8

/-! ## Attacking planeswalkers and Tomik, Orzhov Lawmage (ruling 834) -/

/-- The opponent controls a planeswalker (and Tomik); Grizzly Bears and Hill
Giant are ready to attack. -/
def attackingPlaneswalkerSetup (withTomik : Bool) : Game :=
  let g := addPermanent (addPermanent afterDraw grizzlyBears me me) hillGiant me me
  let g := withLoyalty (addPermanent g ajaniResolute opp opp) "Ajani Resolute" 5
  let g := if withTomik then addPermanent g tomikOrzhovLawmage opp opp else g
  skipToPending (passBoth (skipTo g .beginningOfCombat 80)) .declareAttackers 80

#guard
  let g := attackingPlaneswalkerSetup false
  let ajani := namedPermanent g "Ajani Resolute"
  let g := mustApply g me (.declareAttackers #[(namedPermanent g "Hill Giant").id] none #[] #[some ajani.id])
  let g := settle (skipTo (skipToPending g .declareBlockers 80 |> fun g =>
    mustApply g opp (.declareBlockers #[])) .postcombatMain 80)
  loyaltyOf g "Ajani Resolute" == 2 && life g opp == 20

#guard (fraRuling 834).comment.contains "attacking any planeswalker"
#guard
  let g := attackingPlaneswalkerSetup true
  let ajani := namedPermanent g "Ajani Resolute"
  let both := #[(namedPermanent g "Grizzly Bears").id, (namedPermanent g "Hill Giant").id]
  (g.apply me (.declareAttackers both none #[] #[some ajani.id, some ajani.id])).toOption.isNone &&
    (g.apply me (.declareAttackers both none #[] #[some ajani.id, none])).toOption.isSome &&
    ((attackingPlaneswalkerSetup false).apply me
      (.declareAttackers both none #[] #[some ajani.id, some ajani.id])).toOption.isSome

/- Gideon the Oathless: Ward—Discard a card. -/
#guard
  let g := addPermanent afterDraw gideonTheOathless me me
  let g := mustApply g me .pass
  let g := castFra g shock [tgt g "Gideon the Oathless"] opp
  match g.pending with
  | .payWard q _ .discardCard => q == opp
  | _ => false

/-! ## Prowess and Lotus tokens -/

/- Prowess triggers for each noncreature spell you cast; Ruric Thar,
Biomagus has two instances (CR 702.108b). -/
#guard
  let g := addPermanent afterDraw ruricTharBiomagus me me
  let g := settle (castFra g shock [.target (.player opp)])
  power g "Ruric Thar, Biomagus" == 6 && toughness g "Ruric Thar, Biomagus" == 8
#guard
  let g := addPermanent afterDraw tomikIzzetSparkmage me me
  let g := settle (castFra g shock [.target (.player opp)])
  let pumped := power g "Tomik, Izzet Sparkmage" == 2
  let g := settle (castFra g grizzlyBears)
  pumped && power g "Tomik, Izzet Sparkmage" == 2

/- A Lotus token from Kwia Vigorbloom taps and is sacrificed for three mana
of one color. -/
#guard
  let g := addPermanent afterDraw kwiaVigorbloom me me
  let g := settle (g.gainLife me 1)
  onBattlefield g "Lotus"
#guard
  let g := afterDraw.createKindTokens me .lotus 1
  let g := mustApply g me (.tapForMana (namedPermanent g "Lotus").id (.colored .green))
  (g.player me).manaPool.green == 3 && !onBattlefield g "Lotus"

end Mtg.Engine.FraCardTests3
