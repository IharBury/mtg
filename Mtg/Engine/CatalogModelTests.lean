import Mtg.Engine.FraOracleTests8

/-!
# Catalog cards: abilities that used to have no effect

Game-state checks for abilities of HOB, HOC, and MSH cards that were parsed
but never happened in a game: triggers whose events were never fired,
subtype filters that were ignored, and Crew.
-/

namespace Mtg.Engine.CatalogModelTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests
open Mtg.Engine.FraRulingTests
open Mtg.Engine.FraCardTests
open Mtg.Engine.FraCardTests2
open Mtg.Engine.FraCardTests3

def creatureTokens (g : Game) (p : PlayerId) : Nat :=
  ((g.permanentsOf p).filter (fun o => o.isCreature && o.printed.isToken)).size

def treasures (g : Game) (p : PlayerId) : Nat :=
  ((g.permanentsOf p).filter (fun o => g.hasSubtype o "Treasure")).size

/-! ## “This or another [subtype] you control enters” -/

/- Fíli the Pathfinder makes a Dwarf for a nontoken Dwarf, not for other
permanents. -/
#guard
  let g := addPermanent afterDraw filiThePathfinder me me
  let g := settle (enterPermanent g grizzlyBears me)
  creatureTokens g me == 0
#guard
  let g := addPermanent afterDraw filiThePathfinder me me
  let g := settle (enterPermanent g bofurReliableGuardian me)
  creatureTokens g me == 1

/- Thorin, King of Durin's Folk makes a Treasure for himself and other
Dwarves only. -/
#guard
  let g := settle (enterPermanent afterDraw thorinKingOfDurinsFolk me)
  let one := treasures g me == 1
  let g := settle (enterPermanent g grizzlyBears me)
  let g := settle (enterPermanent g bofurReliableGuardian me)
  one && treasures g me == 2

/- Kíli the Resourceful draws for another Dwarf or an Equipment. -/
#guard
  let g := addPermanent afterDraw kiliTheResourceful me me
  let before := handSize g me
  let g := settle (enterPermanent g grizzlyBears me)
  let none_ := handSize g me == before
  let g := settle (enterPermanent g dunedainBlade me)
  none_ && handSize g me == before + 1

/-! ## Cast triggers -/

/- Necklace of Girion: casting a green spell puts a +1/+1 counter on target
creature you control. -/
#guard
  let g := addPermanent (addPermanent afterDraw necklaceOfGirion me me) grizzlyBears me me
  let g := settle (castFra g giantGrowth [tgt g "Grizzly Bears"])
  counters g "Grizzly Bears" == 1

/- Smaug, Wicked Worm: a spell paid with Treasure mana draws a card and loses
1 life. -/
#guard
  let g := addPermanent afterDraw smaugWickedWorm me me
  let g := g.createKindTokens me .treasure 1
  let g := mustApply g me (.tapForMana (namedPermanent g "Treasure").id (.colored .red))
  let before := handSize g me
  let g := addToHand g shock me
  let g := mustApply g me (.cast (handObj g me "Shock").id)
  let g := mustApply g me (.target (.player opp))
  let g := settle (mustApply g me .pay)
  handSize g me == before + 1 && life g me == 19 && life g opp == 18
/- Without Treasure mana, nothing happens. -/
#guard
  let g := addPermanent afterDraw smaugWickedWorm me me
  let g := settle (castFra g shock [.target (.player opp)])
  life g me == 20

/- Baron Helmut Zemo connives when you cast a black spell from your hand. -/
#guard
  let g := addPermanent afterDraw baronHelmutZemo me me
  let before := (g.player me).graveyard.size
  let g := settle (castFra g (fromOracleKeeping ["Night's Whisper", "{1}{B}", "Sorcery",
    "You draw two cards and you lose 2 life."]))
  (g.player me).graveyard.size ≥ before + 2

/-! ## Combat, upkeep, and tapping -/

/- Bolg, Erebor's Reckoning: at the beginning of each combat, other Goblins and
Orcs you control get +2/+2 and opponents' creatures shrink by one. -/
#guard
  let g := addPermanent (addPermanent withBears bolgEreborsReckoning me me) bolgsCompany me me
  let g := settle (passBoth (skipTo g .beginningOfCombat 80))
  power g "Bolg's Company" == 4 && power g "Grizzly Bears" == 1

/- Rewrite History: tapping creatures loots and adds a plan counter. -/
#guard
  let g := addPermanent (addPermanent afterDraw rewriteHistory me me) grizzlyBears me me
  let g := g.becomeTapped (namedPermanent g "Grizzly Bears")
  let g := settle g
  (namedPermanent g "Rewrite History").status.plan == 1

/- Super Intelligence: the enchanted creature's controller draws at their
upkeep. -/
#guard
  let g := addPermanent (addPermanent afterDraw grizzlyBears me me) superIntelligence me me
  let g := equip g "Super Intelligence" "Grizzly Bears"
  let g := skipTo (skipTo g .end 300) .upkeep 300
  let g := skipTo (skipTo (applyIdle g) .end 300) .upkeep 300
  let before := handSize g me
  let g := settle g
  g.activePlayer == me && handSize g me == before + 1

/- Super-Soldier Serum attaches your Equipment when the creature attacks. -/
#guard
  let g := addPermanent (addPermanent afterDraw grizzlyBears me me) superSoldierSerum me me
  let g := addPermanent g dunedainBlade me me
  let g := equip g "Super-Soldier Serum" "Grizzly Bears"
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g me (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])
  let g := stackTriggers g
  let g := mustApply g me (.targets #[perm g "Dúnedain Blade"])
  let g := settle g
  (namedPermanent g "Dúnedain Blade").attachedTo == some (namedPermanent g "Grizzly Bears").id

/- The Thing, Ben Grimm gets two counters when Heroes you control deal damage
to a player. -/
#guard
  let g := addPermanent (addPermanent afterDraw theThingBenGrimm me me) braveBrawler me me
  let g := attackThen g #["Brave Brawler"]
  counters g "The Thing, Ben Grimm" == 2

/-! ## Leaving the battlefield, drawing, and discarding -/

/- Thunderbolts Conspiracy returns a dying Villain with a finality counter as
a Hero. -/
#guard
  let g := addPermanent (addPermanent afterDraw thunderboltsConspiracy me me) aerialDoombot me me
  let g := settle (g.sacrificeToGraveyard (namedPermanent g "Aerial Doombot") "sacrificed")
  let bot := namedPermanent g "Aerial Doombot"
  bot.status.finality == 1 && g.hasSubtype bot "Hero"

/- Justice, Vance Astrovik gets a counter when another nonland permanent you
control returns to hand. -/
#guard
  let g := addPermanent (addPermanent afterDraw justiceVanceAstrovik me me) grizzlyBears me me
  let g := settle (g.returnToHand (namedPermanent g "Grizzly Bears").id me)
  counters g "Justice, Vance Astrovik" == 1

/- King T'Challa: when any player draws their second card each turn, you draw. -/
#guard
  let g := addPermanent afterDraw kingTChalla me me
  let g := g.modifyPlayer opp (fun pl => { pl with cardsDrawnThisTurn := 0 })
  let before := handSize g me
  let g := settle (g.draw opp 2)
  handSize g me == before + 1

/- Moonstone, Harsh Mistress exiles a discarded card, which you may play. -/
#guard
  let g := addPermanent (addToHand afterDraw shock me) moonstoneHarshMistress me me
  let g := g.discardFromHand me (handObj g me "Shock").id
  let g := settle g
  inExile g "Shock" &&
    g.canCast me ((g.objects.find? (fun o => o.zone == .exile && o.name == "Shock")).get!)

/-! ## Crew -/

/- Dependable Quinjet (Crew 4) becomes an artifact creature after tapping
creatures with total power 4 or more; not enough power can't crew it. -/
#guard
  let g := addPermanent (addPermanent afterDraw dependableQuinjet me me) grizzlyBears me me
  let quinjet := namedPermanent g "Dependable Quinjet"
  !quinjet.isCreature && activationRejected g quinjet "Crew"
#guard
  let g := addPermanent afterDraw dependableQuinjet me me
  let g := addPermanent (addPermanent g grizzlyBears me me) grayOgre me me
  let quinjet := namedPermanent g "Dependable Quinjet"
  let g := mustApply g me (.activate quinjet.id (abIdx g quinjet "Crew"))
  let g := mustApply g me (.choosePermanents #[(namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Gray Ogre").id])
  let g := resolved g
  let quinjet := namedPermanent g "Dependable Quinjet"
  quinjet.isCreature && g.power quinjet == 3 && (namedPermanent g "Gray Ogre").status.tapped &&
    g.canAttack quinjet

/-! ## Modal spells with more than one mode -/

/- Pinecone Strike (choose one or both): 3 damage to a creature and destroy an
artifact token, each with its own target. -/
#guard
  let g := withGiant.createKindTokens opp .treasure 1
  let g := resolved (castFra g pineconeStrike
    [.chooseMode 0, .chooseMode 1, tgt g "Hill Giant", tgt g "Treasure"])
  inExile g "Hill Giant" && treasures g opp == 0
/- Choosing just one mode still works; declining stops after the first mode,
and a mode with no legal target isn't offered. -/
#guard
  let g := withGiant.createKindTokens opp .treasure 1
  let g := resolved (castFra g pineconeStrike [.chooseMode 0, .decline, tgt g "Hill Giant"])
  inExile g "Hill Giant" && treasures g opp == 1
#guard
  let g := resolved (castFra withGiant pineconeStrike [.chooseMode 0, tgt withGiant "Hill Giant"])
  inExile g "Hill Giant"

/- Flame of Anor: two modes only while you control a Wizard. -/
#guard
  let g := addPermanent withGiant gandalfSparkStarter me me
  let before := handSize g me
  let g := resolved (castFra g flameOfAnor
    [.chooseMode 0, .chooseMode 2, .target (.player me), tgt g "Hill Giant"])
  !onBattlefield g "Hill Giant" && handSize g me == before + 2
#guard
  let g := everyColor (addToHand withGiant flameOfAnor me) me
  let g := mustApply g me (.cast (handObj g me "Flame of Anor").id)
  let g := mustApply g me (.chooseMode 2)
  match g.pending with
  | .chooseTargets _ => true
  | _ => false

/- Murdock's Crusade: paying teamwork chooses both modes. -/
#guard
  let g := addPermanent (addPermanent afterDraw hillGiant me me) grizzlyBears me me
  let g := addPermanent (addPermanent g crawWurm opp opp) wayOfTheWildspeaker opp opp
  let g := everyColor (addToHand g murdockSCrusade me) me
  let g := mustApply g me (.cast (handObj g me "Murdock's Crusade").id)
  let g := mustApply g me (.chooseMode 0)
  let g := mustApply g me (.announceTeamwork true)
  let g := mustApply g me (.choosePermanents #[(namedPermanent g "Hill Giant").id,
    (namedPermanent g "Grizzly Bears").id])
  let g := mustApply g me (tgt g "Craw Wurm")
  let g := mustApply g me (tgt g "Way of the Wildspeaker")
  let g := resolved (mustApply g me .pay)
  inExile g "Craw Wurm" && inExile g "Way of the Wildspeaker"

/-! ## Activation costs paid with chosen objects (CR 601.2h / 602.2b) -/

def pick (g : Game) (ids : Array ObjectId) : Game := mustApply g me (.choosePermanents ids)

def pickRejected (g : Game) (ids : Array ObjectId) : Bool :=
  match g.apply me (.choosePermanents ids) with
  | .error _ => true
  | .ok _ => false

def choosingCost (g : Game) : Bool :=
  match g.pending with
  | .fraChoice q (.costPicks ..) => q == me
  | _ => false

def idOf (g : Game) (name : String) : ObjectId := (namedPermanent g name).id

def choosingPick (g : Game) : Bool :=
  match g.pending with
  | .fraChoice q (.mayPayPickThen ..) => q == me
  | _ => false

/- Kingpin's Enforcers: the player chooses the artifact or creature to
sacrifice. -/
def enforcersBoard : Game :=
  let g := addPermanent (addPermanent afterDraw kingpinSEnforcers me me) grizzlyBears me me
  addPermanent g murmuringVolume me me
#guard
  let g := activateNamed enforcersBoard "Kingpin's Enforcers" "Draw"
  let before := handSize g me
  let g := resolved (pick g #[idOf g "Grizzly Bears"])
  choosingCost (activateNamed enforcersBoard "Kingpin's Enforcers" "Draw") &&
    !onBattlefield g "Grizzly Bears" && onBattlefield g "Murmuring Volume" &&
    handSize g me == before + 1
/- A land can't pay it, and declining cancels the activation and returns the
mana (CR 733.1). -/
#guard
  let g := addPermanent enforcersBoard forest me me
  let g := activateNamed g "Kingpin's Enforcers" "Draw"
  let pool := (g.player me).manaPool.total
  let undone := mustApply g me .decline
  pickRejected g #[idOf g "Forest"] && g.stack.size == 1 && undone.stack.isEmpty &&
    (undone.player me).manaPool.total == pool + 3 && undone.pending == .none &&
    onBattlefield undone "Grizzly Bears"

/- Bullseye, Death Dealer: discard a nonland card instead of sacrificing an
artifact. A land card can't be discarded for it. -/
#guard
  let g := addPermanent (addPermanent afterDraw bullseyeDeathDealer me me) murmuringVolume me me
  let g := addToHand (addToHand g shock me) forest me
  let g := activateNamed g "Bullseye, Death Dealer" "2 damage" [.target (.player opp)]
  let forestId := (handObj g me "Forest").id
  let g' := resolved (pick g #[(handObj g me "Shock").id])
  pickRejected g #[forestId] && life g' opp == 18 && inGraveyard g' me "Shock" &&
    onBattlefield g' "Murmuring Volume"

/- The Astonishing Ant-Man removes the chosen number of +1/+1 counters and
creates that many Insects. -/
#guard
  let g := plusOnes (addPermanent afterDraw theAstonishingAntMan me me) "The Astonishing Ant-Man" 3
  let g := resolved (activateNamed g "The Astonishing Ant-Man" "Insect" [.chooseX 2])
  creatureTokens g me == 2 && counters g "The Astonishing Ant-Man" == 1
#guard
  let g := plusOnes (addPermanent afterDraw theAstonishingAntMan me me) "The Astonishing Ant-Man" 3
  activationRejected g (namedPermanent g "The Astonishing Ant-Man") "Insect" [.chooseX 4]

/- Jessica Jones, Private Eye gets a stun counter as the cost is paid. -/
#guard
  let g := addPermanent afterDraw jessicaJonesPrivateEye me me
  let g := activateNamed g "Jessica Jones, Private Eye" "Exile the top"
  (namedPermanent g "Jessica Jones, Private Eye").status.stun == 1 && g.stack.size == 1

/- Ronin, Shadow Stalker sacrifices an Equipment attached to it, not another
Equipment. -/
def roninBoard : Game :=
  let g := addPermanent (addPermanent afterDraw roninShadowStalker me me) dunedainBlade me me
  let g := equip g "Dúnedain Blade" "Ronin, Shadow Stalker"
  addPermanent (addPermanent g huntersAxe me me) grizzlyBears opp opp
#guard
  let g := activateNamed roninBoard "Ronin, Shadow Stalker" "Target creature gets" [tgt roninBoard "Grizzly Bears"]
  let g' := resolved (pick g #[idOf g "Dúnedain Blade"])
  pickRejected g #[idOf g "Hunter's Axe"] && !onBattlefield g' "Grizzly Bears" &&
    !onBattlefield g' "Dúnedain Blade" && onBattlefield g' "Hunter's Axe"
#guard
  let g := addPermanent (addPermanent afterDraw roninShadowStalker me me) huntersAxe me me
  let g := addPermanent g grizzlyBears opp opp
  activationRejected g (namedPermanent g "Ronin, Shadow Stalker") "Target creature gets"

/- The Shire taps the chosen untapped creature. -/
#guard
  let g := addPermanent (addPermanent (addPermanent afterDraw theShire me me) grizzlyBears me me) hillGiant me me
  let g := activateNamed g "The Shire" "Food"
  let g := resolved (pick g #[idOf g "Hill Giant"])
  (namedPermanent g "Hill Giant").status.tapped && !(namedPermanent g "Grizzly Bears").status.tapped &&
    (g.permanentsOf me).any (fun o => g.hasSubtype o "Food")

/- Tom, Bert, and William sacrifice another creature (not themselves) and draw
cards equal to its power, then discard a card. -/
#guard
  let g := addPermanent (addPermanent afterDraw tomBertAndWilliam me me) hillGiant me me
  let g := addPermanent g grizzlyBears me me
  let g := activateNamed g "Tom, Bert, and William" "Draw cards"
  let before := handSize g me
  let g' := resolved (pick g #[idOf g "Hill Giant"])
  pickRejected g #[idOf g "Tom, Bert, and William"] && !onBattlefield g' "Hill Giant" &&
    onBattlefield g' "Grizzly Bears" && handSize g' me == before + 3 - 1

/- Misty Knight, Hero for Hire discards the chosen card. -/
#guard
  let g := addPermanent afterDraw mistyKnightHeroForHire me me
  let g := addToHand (addToHand g shock me) giantGrowth me
  let g := activateNamed g "Misty Knight, Hero for Hire" "Draw a card"
  let g := resolved (pick g #[(handObj g me "Giant Growth").id])
  inGraveyard g me "Giant Growth" && inHand g me "Shock"

/- Key to the Side-Door discards a legendary card with the same name as a
legendary permanent you control. -/
#guard
  let g := addPermanent (addPermanent afterDraw keyToTheSideDoor me me) mistyKnightHeroForHire me me
  let g := addToHand (addToHand g mistyKnightHeroForHire me) roninShadowStalker me
  let g := activateNamed g "Key to the Side-Door" "Draw two"
  let before := handSize g me
  let g' := resolved (pick g #[(handObj g me "Misty Knight, Hero for Hire").id])
  pickRejected g #[(handObj g me "Ronin, Shadow Stalker").id] &&
    inGraveyard g' me "Misty Knight, Hero for Hire" && handSize g' me == before + 1

/-- Mana `p` spends activating ability `idx` of `id` with `steps`. -/
def manaSpent (g : Game) (id : ObjectId) (idx : Nat) (steps : List Action) : Nat :=
  let g := everyColor g me 6
  let before := (g.player me).manaPool.total
  let g := mustApply g me (.activate id idx)
  let g := steps.foldl (fun g a => mustApply g me a) g
  let g := match g.pending with
    | .activateManaAbilities _ => mustApply g me .pay
    | _ => g
  before - (g.player me).manaPool.total

/- Raft Security Officer costs {1} less if it targets a creature with power 3
or less. -/
#guard
  let g := addPermanent (addPermanent afterDraw raftSecurityOfficer me me) grizzlyBears opp opp
  let g := addPermanent g crawWurm opp opp
  let o := namedPermanent g "Raft Security Officer"
  manaSpent g o.id 0 [tgt g "Grizzly Bears"] == 1 && manaSpent g o.id 0 [tgt g "Craw Wurm"] == 2

/- Minas Tirith: two creatures attacked this turn, even after combat ends. -/
#guard
  let g := addPermanent (addPermanent afterDraw minasTirith me me) grizzlyBears me me
  let g := addPermanent g hillGiant me me
  let g := attackThen g #["Grizzly Bears", "Hill Giant"]
  let before := handSize g me
  handSize (resolved (activateNamed g "Minas Tirith" "Draw a card")) me == before + 1
#guard
  let g := addPermanent (addPermanent afterDraw minasTirith me me) grizzlyBears me me
  let g := addPermanent g hillGiant me me
  let g := attackThen g #["Grizzly Bears"]
  activationRejected g (namedPermanent g "Minas Tirith") "Draw a card"

/- Dwarven Mauler: equip abilities targeting it cost {2} less. -/
#guard
  let g := addPermanent (addPermanent afterDraw dwarvenMauler me me) grizzlyBears me me
  let g := addPermanent g huntersAxe me me
  let axe := namedPermanent g "Hunter's Axe"
  manaSpent g axe.id (abIdx g axe "Attach") [tgt g "Dwarven Mauler"] == 0 &&
    manaSpent g axe.id (abIdx g axe "Attach") [tgt g "Grizzly Bears"] == 2

/- Kíli the Resourceful: with an enduring story, the first equip ability each
turn costs {0}; the next one costs its equip cost. -/
#guard
  let g := addPermanent (addPermanent afterDraw kiliTheResourceful me me) grizzlyBears me me
  let g := addPermanent (addPermanent g huntersAxe me me) huntersAxe me me
  let g := g.modifyPlayer me (fun pl => { pl with enduringStory := true })
  let axes := ((g.permanentsOf me).filter (·.name == "Hunter's Axe")).map (·.id)
  let idx := abIdx g (g.object! axes[0]!) "Attach"
  let first := manaSpent g axes[0]! idx [tgt g "Grizzly Bears"]
  let g := resolved (activateId g axes[0]! idx [tgt g "Grizzly Bears"])
  let second := manaSpent g axes[1]! idx [tgt g "Grizzly Bears"]
  first == 0 && second == 2
#guard
  let g := addPermanent (addPermanent afterDraw kiliTheResourceful me me) grizzlyBears me me
  let g := addPermanent g huntersAxe me me
  let axe := namedPermanent g "Hunter's Axe"
  manaSpent g axe.id (abIdx g axe "Attach") [tgt g "Grizzly Bears"] == 2

/- Allure of Power (My Precious's Adventure) sacrifices a creature as an
additional cost; an artifact can't pay it. -/
#guard
  let g := addPermanent (addPermanent afterDraw grizzlyBears me me) murmuringVolume me me
  let g := everyColor (addToHand g myPrecious me) me
  let before := handSize g me
  let g := mustApply g me (.castAdventure (handObj g me "My Precious").id)
  let g := mustApply g me .pay
  let rejected :=
    match g.apply me (.sacrifice (idOf g "Murmuring Volume")) with
    | .error _ => true
    | .ok _ => false
  let g := resolved (mustApply g me (.sacrifice (idOf g "Grizzly Bears")))
  rejected && !onBattlefield g "Grizzly Bears" && onBattlefield g "Murmuring Volume" &&
    handSize g me == before - 1 + 2
#guard
  let g := addPermanent afterDraw murmuringVolume me me
  let g := everyColor (addToHand g myPrecious me) me
  match g.apply me (.castAdventure (handObj g me "My Precious").id) with
  | .error _ => true
  | .ok _ => false

/- Bullseye, Death Dealer: when it enters, you may discard a nonland card;
when you do, it deals 2 damage to any target. Declining deals no damage. -/
#guard
  let g := addToHand (addToHand afterDraw shock me) forest me
  let g := stackTriggers (enterPermanent g bullseyeDeathDealer me)
  let g := resolveTop g
  let offered := choosingPick g
  let g := mustApply g me (.choosePermanents #[(handObj g me "Shock").id])
  let g := mustApply (stackTriggers g) me (.target (.player opp))
  let g := settle g
  offered && life g opp == 18 && inGraveyard g me "Shock" && inHand g me "Forest"
#guard
  let g := addToHand afterDraw shock me
  let g := resolveTop (stackTriggers (enterPermanent g bullseyeDeathDealer me))
  let g := settle (mustApply g me .decline)
  life g opp == 20 && inHand g me "Shock"

/-! ## Mana abilities (CR 605) -/

def pool (g : Game) : ManaPool := (g.player me).manaPool

def manaIdx (g : Game) (name : String) (pred : Game.ManaAbilityDef → Bool) : Nat :=
  let defs := g.manaAbilityDefs (namedPermanent g name)
  ((List.range defs.size).find? (fun i => pred defs[i]!)).getD 0

def tapFor (g : Game) (name : String) (m : ManaType) : Game :=
  mustApply g me (.tapForMana (idOf g name) m)

def manaRejected (g : Game) (a : Action) : Bool :=
  match g.apply me a with
  | .error _ => true
  | .ok _ => false

/- Arc Reactor adds {C}{C}{C} immediately, without using the stack. -/
#guard
  let g := tapFor (addPermanent afterDraw arcReactor me me) "Arc Reactor" .colorless
  (pool g).colorless == 3 && g.stack.isEmpty

/- Bolg's Company sacrifices the chosen other Goblin and adds {B}{R}. -/
#guard
  let g := addPermanent (addPermanent afterDraw bolgsCompany me me) bolgsCompany me me
  let ids := ((g.permanentsOf me).filter (·.name == "Bolg's Company")).map (·.id)
  let o := g.object! ids[0]!
  let i := manaIdx g "Bolg's Company" (!·.picks.isEmpty)
  let g' := mustApply g me (.activateManaAbility o.id i #[.colored .black, .colored .red] #[ids[1]!])
  (pool g').black == 1 && (pool g').red == 1 && g'.stack.isEmpty &&
    (g'.object! o.id).status.tapped && !(g'.findObject? ids[1]!).any (·.isOnBattlefield) &&
    manaRejected g (.tapForMana o.id (.colored .black)) &&
    manaRejected g (.activateManaAbility o.id i #[.colored .black, .colored .red] #[o.id])

/- Mount Doom: {T}, Pay 1 life: Add {B} or {R}. -/
#guard
  let g := tapFor (addPermanent afterDraw mountDoom me me) "Mount Doom" (.colored .red)
  (pool g).red == 1 && life g me == 19

/- Fíli and Kíli, Joyous add {R}{R} spendable only on Dwarf, Equipment, and
Saga spells. -/
#guard
  let g := tapFor (addPermanent afterDraw filiAndKiliJoyous me me) "Fíli and Kíli, Joyous" (.colored .red)
  (pool g).red == 2 &&
    (pool g).fraRestricted == #[(.colored .red, .dwarfEquipmentSagaSpell), (.colored .red, .dwarfEquipmentSagaSpell)]

/- Relic of Sauron adds two mana in any combination of {U}, {B}, and {R}. -/
#guard
  let g := addPermanent afterDraw relicOfSauron me me
  let o := namedPermanent g "Relic of Sauron"
  let g' := mustApply g me (.activateManaAbility o.id 0 #[.colored .blue, .colored .black])
  (pool g').blue == 1 && (pool g').black == 1 &&
    manaRejected g (.activateManaAbility o.id 0 #[.colored .green, .colored .blue])

/- Giant's Boulder spends {1} from the pool to add one mana of any color. -/
#guard
  let g := withMana (addPermanent afterDraw giantsBoulder me me) me .white 1
  let g := tapFor g "Giant's Boulder" (.colored .green)
  (pool g).green == 1 && (pool g).white == 0 && g.stack.isEmpty

/- Baxter Building: {4}, {T}: four mana in any combination of colors. -/
#guard
  let g := withMana (addPermanent afterDraw baxterBuilding me me) me .green 4
  let o := namedPermanent g "Baxter Building"
  let i := manaIdx g "Baxter Building" (·.cost.includesManaPayment)
  let g := mustApply g me (.activateManaAbility o.id i
    #[.colored .white, .colored .blue, .colored .black, .colored .red])
  (pool g).white == 1 && (pool g).blue == 1 && (pool g).black == 1 && (pool g).red == 1 &&
    (pool g).green == 0

/- Ronin, Shadow Stalker: Pay 2 life for two mana of one color spendable on
Equipment; only once each turn. -/
#guard
  let g := addPermanent afterDraw roninShadowStalker me me
  let o := namedPermanent g "Ronin, Shadow Stalker"
  let i := manaIdx g "Ronin, Shadow Stalker" (·.payLife == 2)
  let g := mustApply g me (.activateManaAbility o.id i #[.colored .black, .colored .black])
  (pool g).black == 2 && life g me == 18 && !(namedPermanent g "Ronin, Shadow Stalker").status.tapped &&
    (pool g).fraRestricted.all (·.2 == .equipmentOrEquip) &&
    manaRejected g (.activateManaAbility o.id i #[.colored .black, .colored .black])

/- Doc Samson adds X mana of one color, X = its power. -/
#guard
  let g := addPermanent afterDraw docSamsonSuperPsychiatrist me me
  let pw := power g "Doc Samson, Super Psychiatrist"
  let g := tapFor g "Doc Samson, Super Psychiatrist" (.colored .blue)
  ((pool g).blue : Int) == pw && pw > 0

/- Hydraulic Helper's {U} can't be spent on a nonartifact spell. -/
#guard
  let g := tapFor (addPermanent afterDraw hydraulicHelper me me) "Hydraulic Helper" (.colored .blue)
  (pool g).cantNonartifactBlue == 1

/- Castle Doom's colored mana may be spent only to cast an artifact spell. -/
#guard
  let g := addPermanent afterDraw castleDoom me me
  let o := namedPermanent g "Castle Doom"
  let i := manaIdx g "Castle Doom" (·.restriction == .fra .artifactSpell)
  let g := mustApply g me (.activateManaAbility o.id i #[.colored .red])
  (pool g).fraRestricted == #[(.colored .red, .artifactSpell)]

/- Chandra, Torch of Defiance's +1 that adds {R}{R} is a loyalty ability, so it
uses the stack (CR 605.1a). -/
#guard
  let g := pw chandraTorchOfDefiance 4
  let o := namedPermanent g "Chandra, Torch of Defiance"
  let g := mustApply g me (.activate o.id (abIdx g o "Add"))
  g.stack.size == 1 && (pool g).red == 0 && (pool (passBoth g)).red == 2

/- The Black Gate: pay 3 life as it enters, or it enters tapped. -/
#guard
  let g := addToHand afterDraw theBlackGate me
  let g := mustApply g me (.playLand (handObj g me "The Black Gate").id)
  let paid := mustApply g me .accept
  let tapped := mustApply g me .decline
  life paid me == 17 && !(namedPermanent paid "The Black Gate").status.tapped &&
    life tapped me == 20 && (namedPermanent tapped "The Black Gate").status.tapped

/- Delighted Halfling's legendary-only mana makes the spell uncounterable. -/
#guard
  let g := withMana (addPermanent afterDraw delightedHalfling me me) me .white 3
  let g := tapFor g "Delighted Halfling" (.colored .green)
  let g := addToHand g celebornTheWise me
  let g := mustApply g me (.cast (handObj g me "Celeborn the Wise").id)
  let g := mustApply g me .pay
  let spell := (g.stack.back?.map (·.objectId)).getD ⟨0⟩
  let g := g.counterStackSpell spell
  (g.findObject? spell).any (·.zone == .stack)
/- Its colored mana can't pay for a nonlegendary spell. -/
#guard
  let g := tapFor (addPermanent afterDraw delightedHalfling me me) "Delighted Halfling" (.colored .red)
  (pool g).fraRestricted == #[(.colored .red, .legendarySpell)]

/- Desolation of Smaug: the player chooses the colors of four mana that can be
spent only on Dragon spells. -/
#guard
  let g := castFra afterDraw desolationOfSmaug
  let g := passBoth g
  let g := [3, 3, 0, 4].foldl (fun g i => mustApply g me (.chooseMode i)) g
  let restricted := (pool g).fraRestricted.filter (·.2 == .dragonSpell)
  restricted.size == 4 && (restricted.filter (·.1 == .colored .red)).size == 2

/-! ## Extort and “you may pay … When you do” triggers -/

/- The Kingpin of Crime: extort triggers on cast, and paying {W/B} drains each
opponent for 1. -/
#guard
  let g := addPermanent afterDraw theKingpinOfCrime me me
  let g := castFra g shock [.target (.player opp)]
  let g := passBoth (stackTriggers g)
  let offered := match g.pending with
    | .fraChoice _ (.mayPayExtort _) => true
    | _ => false
  let g := settle (mustApply g me .accept)
  offered && life g opp == 17 && life g me == 21
#guard
  let g := addPermanent afterDraw theKingpinOfCrime me me
  let g := castFra g shock [.target (.player opp)]
  let g := settle (mustApply (passBoth (stackTriggers g)) me .decline)
  life g opp == 18 && life g me == 20

/- Spider-Man, To the Rescue: tapping him is optional; the reflexive ability
targets another nonattacking creature you control. -/
#guard
  let g := addPermanent afterDraw grizzlyBears me me
  let g := resolveTop (stackTriggers (enterPermanent g spiderManToTheRescue me))
  let g := mustApply g me .accept
  let selfRejected :=
    match g.apply me (tgt g "Spider-Man, To the Rescue") with
    | .error _ => true
    | .ok _ => false
  let g := passBoth (mustApply g me (tgt g "Grizzly Bears"))
  selfRejected && (namedPermanent g "Spider-Man, To the Rescue").status.tapped &&
    (kw g "Grizzly Bears").indestructible
#guard
  let g := addPermanent afterDraw grizzlyBears me me
  let g := resolveTop (stackTriggers (enterPermanent g spiderManToTheRescue me))
  let g := mustApply g me .decline
  !(namedPermanent g "Spider-Man, To the Rescue").status.tapped && g.stack.isEmpty

/- Killmonger: the player chooses which other creature to sacrifice, then
targets a nonland permanent an opponent controls. -/
#guard
  let g := addPermanent (addPermanent afterDraw grizzlyBears me me) hillGiant me me
  let g := addPermanent g crawWurm opp opp
  let g := resolveTop (stackTriggers (enterPermanent g killmongerScourgeOfWakanda me))
  let g := mustApply g me (.choosePermanents #[idOf g "Hill Giant"])
  let g := passBoth (mustApply g me (tgt g "Craw Wurm"))
  !onBattlefield g "Hill Giant" && onBattlefield g "Grizzly Bears" && !onBattlefield g "Craw Wurm"

/- Hawkeye, Master Marksman: paying {1} once allows one mode; Net stops the
target creature from blocking. -/
#guard
  let g := addPermanent (addPermanent afterDraw hawkeyeMasterMarksman me me) grizzlyBears opp opp
  let hawk := namedPermanent g "Hawkeye, Master Marksman"
  let g := g.applyModeledTrigger me (.onWatch Effect.watchHawkeyeModes) (some hawk.id)
  let g := withMana g me .red 1
  let g := mustApply g me .accept
  let g := mustApply g me (.chooseMode 0)
  let g := passBoth (mustApply g me (tgt g "Grizzly Bears"))
  (namedPermanent g "Grizzly Bears").status.cantBlockUntilEot && (pool g).red == 0

/-! ## Improvise and sneak -/

/- Arc Reactor has improvise: each untapped artifact tapped pays {1}. -/
#guard
  let g := addPermanent (addPermanent afterDraw murmuringVolume me me) murmuringVolume me me
  let vols := ((g.permanentsOf me).filter (·.name == "Murmuring Volume")).map (·.id)
  let g := withMana (addToHand g arcReactor me) me .red 3
  let g := mustApply g me (.cast (handObj g me "Arc Reactor").id)
  let g := mustApply g me (.choosePermanents vols)
  let g := settle (mustApply g me .pay)
  onBattlefield g "Arc Reactor" && vols.all (fun id => (g.object! id).status.tapped) &&
    (pool g).red == 0
/- Improvise pays only generic mana, and a creature spell without improvise
can't use it even with Ironheart granting it to noncreature spells. -/
#guard
  let g := addPermanent (addPermanent afterDraw murmuringVolume me me) ironheartCleverChampion me me
  let g := withMana (addToHand g grizzlyBears me) me .green 4
  let g := mustApply g me (.cast (handObj g me "Grizzly Bears").id)
  match g.apply me (.choosePermanents #[idOf g "Murmuring Volume"]) with
  | .error _ => true
  | .ok _ => false

/- Elektra, Daughter of the Hand: cast for her sneak cost during the declare
blockers step by returning an unblocked attacker; she enters tapped and
attacking. -/
#guard
  let g := addPermanent afterDraw grizzlyBears me me
  let g := addToHand g elektraDaughterOfTheHand me
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g me (.declareAttackers #[idOf g "Grizzly Bears"])
  let g := skipToPending g .declareBlockers 80
  let g := mustApply g opp (.declareBlockers #[])
  let g := withMana (withMana g me .black 2) me .white 1
  let g := mustApply g me (.castWithSneak (handObj g me "Elektra, Daughter of the Hand").id
    (idOf g "Grizzly Bears"))
  let g := mustApply g me .pay
  let g := settle g
  let e := namedPermanent g "Elektra, Daughter of the Hand"
  inHand g me "Grizzly Bears" && e.status.tapped && e.status.attacking
/- Cascade: the player may cast the exiled card without paying its mana cost;
the other exiled cards go to the bottom of the library. -/
#guard
  let g := addToLibraryTop (addToLibraryTop afterDraw lightningBolt me) forest me
  let g := g.resolveCascade me 8
  let g := mustApply g me .accept
  let g := settle (mustApply g me (.target (.player opp)))
  life g opp == 17 && ((g.player me).library[0]?.map (fun id => (g.object! id).name)) == some "Forest"
#guard
  let g := addToLibraryTop afterDraw lightningBolt me
  let g := mustApply (g.resolveCascade me 8) me .decline
  life g opp == 20 && ((g.player me).library[0]?.map (fun id => (g.object! id).name)) == some "Lightning Bolt"

/-! ## Triggered abilities that target: ward and “becomes the target” -/

def killmongerTargets (g : Game) (victim : String) : Game :=
  let g := addPermanent g grizzlyBears me me
  let g := resolveTop (stackTriggers (enterPermanent g killmongerScourgeOfWakanda me))
  let g := mustApply g me (.choosePermanents #[idOf g "Grizzly Bears"])
  mustApply g me (.target (.permanent (theirs g victim).id))

/- Old Fat Spider draws when a triggered ability an opponent controls targets
it. -/
#guard
  let g := addPermanent afterDraw oldFatSpider opp opp
  let before := handSize g opp
  let g := settle (killmongerTargets g "Old Fat Spider")
  handSize g opp == before + 1 && !onBattlefield g "Old Fat Spider"

/- Ward counters a triggered ability unless its controller pays. -/
#guard
  let g := addPermanent afterDraw lakeTownMariners opp opp
  let g := killmongerTargets g "Lake-town Mariners"
  let warded := match g.pending with
    | .payWard q _ (.genericMana 2) => q == me
    | _ => false
  let g := settle (mustApply g me .decline)
  warded && onBattlefield g "Lake-town Mariners"

/-! ## Who triggers on entering -/

/- Thranduil, the Elvenking loots only for another legendary Elf. -/
#guard
  let g := addPermanent afterDraw thranduilTheElvenking me me
  let before := handSize g me
  let g := settle (enterPermanent g llanowarElves me)
  let noLoot := handSize g me == before
  let g := settle (enterPermanent g celebornTheWise me)
  noLoot && handSize g me == before + 1

/- Chief of the Wilds grows only for another Wolf. -/
#guard
  let g := addPermanent afterDraw chiefOfTheWilds me me
  let g := settle (enterPermanent g grizzlyBears me)
  let none_ := counters g "Chief of the Wilds" == 0
  let g := settle (enterPermanent g wargling me)
  none_ && counters g "Chief of the Wilds" == 2

/- Machinesmith Automaton doesn't trigger on itself entering. -/
#guard
  let g := settle (enterPermanent afterDraw machinesmithAutomaton me)
  let alone := counters g "Machinesmith Automaton" == 0
  let g := settle (enterPermanent g murmuringVolume me)
  alone && counters g "Machinesmith Automaton" == 1

/- Mister Fantastic: several tokens entering together trigger once. -/
#guard
  let g := addPermanent afterDraw misterFantasticReedRichards me me
  let g := (g.createKindTokens me .treasure 2).flushTokenEnters
  ((g.waitingTriggers.filter (·.source.name == "Mister Fantastic, Reed Richards")).size == 1)

/- Tokens created by a resolving ability trigger “whenever a token you
control enters” (Belladonna Took). -/
#guard
  let g := addPermanent (addPermanent (addPermanent afterDraw theShire me me) grizzlyBears me me) belladonnaTook me me
  let g := activateNamed g "The Shire" "Food"
  let g := settle (pick g #[idOf g "Grizzly Bears"])
  life g me == 21

/- Part in Friendship triggers only once each turn. -/
#guard
  let g := addPermanent (addPermanent (addPermanent afterDraw partInFriendship me me) grizzlyBears me me) hillGiant me me
  let g := g.destroyPermanent (namedPermanent g "Grizzly Bears")
  let g := stackTriggers g
  let g := g.destroyPermanent (namedPermanent g "Hill Giant")
  let g := stackTriggers g
  (g.stack.filter (fun e => (g.object! e.objectId).name.startsWith "Part in Friendship")).size == 1

/- Landfall works from the graveyard only for Silvan Reveler's “return this
card from your graveyard”, and that ability doesn't work on the battlefield. -/
#guard
  let g := addToGraveyard (addToGraveyard afterDraw attercop me) silvanReveler me
  let g := addPermanent g forest me me
  let g := g.putLandYouControlEntersTriggers (namedPermanent g "Forest")
  g.waitingTriggers.all (·.source.name == "Silvan Reveler") && g.waitingTriggers.size == 1
#guard
  let g := addPermanent afterDraw silvanReveler me me
  let g := addPermanent g forest me me
  let g := g.putLandYouControlEntersTriggers (namedPermanent g "Forest")
  g.waitingTriggers.isEmpty

/- Getaway Barrel triggers when it's put into a graveyard from the
battlefield, though it isn't a creature. -/
#guard
  let g := addPermanent afterDraw getawayBarrel me me
  let g := g.destroyPermanent (namedPermanent g "Getaway Barrel")
  g.waitingTriggers.any (·.source.name == "Getaway Barrel")

/-! ## Intervening “if” clauses (CR 603.4) -/

/- The One Ring gives protection only if it was cast. -/
#guard
  let g := settle (enterPermanent afterDraw theOneRing me)
  !(g.player me).protectionFromEverything
#guard
  let g := resolved (castFra afterDraw theOneRing)
  (g.player me).protectionFromEverything

/- Lake-town Toymaker doesn't trigger unless you've drawn two cards. -/
#guard
  let g := addPermanent (addPermanent afterDraw lakeTownToymaker me me) grizzlyBears me me
  let g := g.modifyPlayer me (fun pl => { pl with cardsDrawnThisTurn := 0 })
  let g := g.putControlledTriggers me .yourBeginCombat
  !g.waitingTriggers.any (·.source.name == "Lake-town Toymaker")

/- Uncover the Moon-Letters: you may draw X, X being the mana spent on the
spell, then discard two. -/
#guard
  let g := addPermanent afterDraw uncoverTheMoonLetters me me
  let g := addToHand (addToHand g grizzlyBears me) hillGiant me
  let g := castFra g shock [.target (.player opp)]
  let g := passBoth (stackTriggers g)
  let offered := match g.pending with
    | .fraChoice _ (.mayDrawThenDiscard 1 2) => true
    | _ => false
  offered

/-- Resolve the top of the stack until a choice is pending. -/
def untilFraChoice (g : Game) : Nat → Game
  | 0 => g
  | n + 1 =>
    match g.pending with
    | .fraChoice .. => g
    | .chooseTriggerToStack q => untilFraChoice (mustApply g q (.stackTriggers (g.defaultTriggerSourceIds q))) n
    | _ => if g.stack.isEmpty then g else untilFraChoice (passBoth g) n

/- The Serpent Society: another creature with deathtouch dying makes each
opponent sacrifice a nontoken creature of their choice. -/
#guard
  let g := addPermanent (addPermanent afterDraw theSerpentSociety me me) theMasterOfLakeTown me me
  let g := addPermanent (addPermanent g grizzlyBears opp opp) hillGiant opp opp
  let g := g.destroyPermanent (namedPermanent g "The Master of Lake-town")
  let g := untilFraChoice (stackTriggers g) 6
  let asked := match g.pending with
    | .fraChoice q (.sacrificeNontokenEach ..) => q == opp
    | _ => false
  let g := settle (mustApply g opp (.choosePermanents #[(theirs g "Hill Giant").id]))
  asked && !g.objects.any (fun o => o.name == "Hill Giant" && o.isOnBattlefield) &&
    (theirs g "Grizzly Bears").isOnBattlefield
#guard
  let g := addPermanent (addPermanent afterDraw theSerpentSociety me me) grizzlyBears me me
  let g := stackTriggers (g.destroyPermanent (namedPermanent g "Grizzly Bears"))
  !g.stack.any (fun e => (g.object! e.objectId).name.startsWith "The Serpent Society")

/- Knight of Wundagore: counters on another creature, not on itself. -/
#guard
  let g := addPermanent (addPermanent afterDraw knightOfWundagore me me) grizzlyBears me me
  let self := g.addPlusOnePlusOneTo (namedPermanent g "Knight of Wundagore") 1
  let other := g.addPlusOnePlusOneTo (namedPermanent g "Grizzly Bears") 1
  !self.waitingTriggers.any (·.source.name == "Knight of Wundagore") &&
    other.waitingTriggers.any (·.source.name == "Knight of Wundagore")

/- Invisible Woman: only counters on other Heroes you control, and the Wall
is optional. -/
#guard
  let g := addPermanent (addPermanent afterDraw invisibleWomanSueStorm me me) grizzlyBears me me
  let g := g.addPlusOnePlusOneTo (namedPermanent g "Grizzly Bears") 1
  !g.waitingTriggers.any (·.source.name == "Invisible Woman, Sue Storm")

/- Storm, Windrider: a spell that targets any creature gives it flying. -/
#guard
  let g := addPermanent (addPermanent afterDraw stormWindrider me me) grizzlyBears opp opp
  let g := castFra g giantGrowth [.target (.permanent (theirs g "Grizzly Bears").id)]
  let g := passBoth (stackTriggers g)
  (kw g "Grizzly Bears").flying || (g.currentKeywords (theirs g "Grizzly Bears")).flying

/- Fin Fang Foom copies an instant or sorcery that targets an artifact or land;
the copy may get a new target. -/
#guard
  let g := addPermanent afterDraw finFangFoom me me
  let g := addPermanent (addPermanent g murmuringVolume opp opp) forest opp opp
  let g := castFra g fireOfOrthanc [.target (.permanent (theirs g "Murmuring Volume").id)]
  let g := passBoth (stackTriggers g)
  let offered := match g.pending with
    | .fraChoice _ (.newTargetsForCopies _) => true
    | _ => false
  let g := settle (mustApply g me (.choosePermanents #[(theirs g "Forest").id]))
  offered && counters g "Fin Fang Foom" == 2 &&
    !g.objects.any (fun o => o.isOnBattlefield && (o.name == "Forest" || o.name == "Murmuring Volume") && o.controlledBy opp)
#guard
  let g := addPermanent (addPermanent afterDraw finFangFoom me me) grizzlyBears opp opp
  let g := stackTriggers (castFra g shock [.target (.permanent (theirs g "Grizzly Bears").id)])
  !g.stack.any (fun e => (g.object! e.objectId).name.startsWith "Fin Fang Foom")

/-! ## Triggered ability resolutions -/

/-- Put triggered ability `idx` of permanent `name` on the stack. -/
def fireTrigger (g : Game) (name : String) (idx : Nat := 0) : Game :=
  let o := namedPermanent g name
  (g.putTriggeredAbilityOnStack me o o.printed.triggeredAbilities[idx]! "test trigger").promptTriggerTargetsIfNeeded

/- Enchanted River's Grasp taps the enchanted creature and removes every counter. -/
#guard
  let g := addPermanent (addPermanent afterDraw grizzlyBears me me) enchantedRiverSGrasp me me
  let g := equip g "Enchanted River's Grasp" "Grizzly Bears"
  let host := namedPermanent g "Grizzly Bears"
  let g := g.setObject { host with status :=
    { host.status with plusOnePlusOne := 2, stun := 1, minusOneMinusOne := 1 } }
  let g := passBoth (fireTrigger g "Enchanted River's Grasp")
  let h := namedPermanent g "Grizzly Bears"
  h.status.tapped && h.status.plusOnePlusOne == 0 && h.status.stun == 0 &&
    h.status.minusOneMinusOne == 0

/- Desert Were-Worm untaps attackers and schedules another combat phase. -/
#guard
  let g := addPermanent afterDraw desertWereWorm me me
  let w := namedPermanent g "Desert Were-Worm"
  let g := g.setObject { w with status := { w.status with attacking := true, tapped := true } }
  let g := passBoth (fireTrigger g "Desert Were-Worm")
  !(namedPermanent g "Desert Were-Worm").status.tapped && g.additionalCombatPhases == 1

/- Celebrate the Mountain-king exiles up to one nonland each opponent controls. -/
#guard
  let g := addPermanent (addPermanent afterDraw mountain opp opp) grizzlyBears opp opp
  let g := addPermanent g celebrateTheMountainKing me me
  let g := fireTrigger g "Celebrate the Mountain-king"
  let g := passBoth (mustApply g me (.target (.permanent (idOf g "Grizzly Bears"))))
  inExile g "Grizzly Bears" && onBattlefield g "Mountain"

/- Bejeweled Warg's combat-damage trigger is a real mode choice. -/
#guard
  let g := addPermanent afterDraw bejeweledWarg me me
  let g := fireTrigger g "Bejeweled Warg"
  let g := mustApply g me (.chooseMode 0)
  let g := passBoth (mustApply g me (.target (.permanent (idOf g "Bejeweled Warg"))))
  counters g "Bejeweled Warg" == 1 && treasures g me == 0
#guard
  let g := addPermanent afterDraw bejeweledWarg me me
  let g := fireTrigger g "Bejeweled Warg"
  let g := passBoth (mustApply g me (.chooseMode 1))
  counters g "Bejeweled Warg" == 0 && treasures g me == 1

/- Bilbo, Thief in the Night may cast an artifact, instant, or sorcery from
the graveyard, paying its cost. Instants and sorceries are exiled instead
of going to the graveyard. Creatures are not offered. -/
#guard
  let g := addPermanent afterDraw bilboThiefInTheNight me me
  let g := addToGraveyard g shock me
  let g := passBoth (fireTrigger g "Bilbo, Thief in the Night")
  let g := mustApply g me .decline
  inGraveyard g me "Shock" && g.stack.isEmpty
#guard
  let g := addPermanent afterDraw bilboThiefInTheNight me me
  let g := addToGraveyard (addToGraveyard g shock me) grizzlyBears me
  let g := withMana g me .red 1
  let g := passBoth (fireTrigger g "Bilbo, Thief in the Night")
  let shockId := (graveyardObj g me "Shock").id
  let offered :=
    match g.pending with
    | .fraChoice _ (.mayCastFromGraveyard ids) =>
      ids.contains shockId && !ids.any (fun id => (g.object! id).name == "Grizzly Bears")
    | _ => false
  let g := mustApply g me (.cast shockId)
  let g := mustApply g me (.target (.player opp))
  let g := passBoth (mustApply g me .pay)
  offered && inExile g "Shock" && !inGraveyard g me "Shock" && life g opp == 18
#guard
  let before := handSize afterDraw me
  let g := addPermanent afterDraw bilboThiefInTheNight me me
  let g := addToGraveyard g nightsWhisper me
  let g := withMana g me .black 1
  let g := passBoth (fireTrigger g "Bilbo, Thief in the Night")
  let g := mustApply g me (.cast (graveyardObj g me "Night's Whisper").id)
  let g := passBoth (mustApply g me .pay)
  inExile g "Night's Whisper" && handSize g me == before + 2 && life g me == 18
#guard
  let g := addPermanent afterDraw bilboThiefInTheNight me me
  let g := addToGraveyard g wayfarersBauble me
  let g := passBoth (fireTrigger g "Bilbo, Thief in the Night")
  let g := passBoth (mustApply g me (.cast (graveyardObj g me "Wayfarer's Bauble").id))
  onBattlefield g "Wayfarer's Bauble" && !inExile g "Wayfarer's Bauble"

/- Elven Raft-Steerer's landfall is modal: tap an opponent's creature or untap
yours. -/
#guard
  let g := addPermanent (addPermanent afterDraw elvenRaftSteerer me me) grizzlyBears opp opp
  let g := fireTrigger g "Elven Raft-Steerer"
  let g := mustApply g me (.chooseMode 0)
  let g := passBoth (mustApply g me (.target (.permanent (theirs g "Grizzly Bears").id)))
  (theirs g "Grizzly Bears").status.tapped

/- Bilbo, Unexpected Adventurer returns a nonland permanent card with mana
value 3 or less from any graveyard under its owner's control. -/
#guard
  let g := addPermanent afterDraw bilboUnexpectedAdventurer me me
  let g := addToGraveyard g grizzlyBears opp
  let g := fireTrigger g "Bilbo, Unexpected Adventurer"
  let card := graveyardObj g opp "Grizzly Bears"
  let g := passBoth (mustApply g me (.target (.card card.id)))
  (theirs g "Grizzly Bears").isOnBattlefield

/- Mirkwood Meditator's landfall is optional. -/
#guard
  let g := fireTrigger (addPermanent afterDraw mirkwoodMeditator me me) "Mirkwood Meditator"
  let g := passBoth g
  let g := mustApply g me .decline
  (namedPermanent g "Mirkwood Meditator").status.setBasePT.isNone

/- Mirkwood Nurturer may return any other permanent you control. -/
#guard
  let g := addPermanent (addPermanent afterDraw mirkwoodNurturer me me) murmuringVolume me me
  let g := fireTrigger g "Mirkwood Nurturer"
  let g := passBoth (mustApply g me (tgt g "Murmuring Volume"))
  inHand g me "Murmuring Volume" && counters g "Mirkwood Nurturer" == 1

/- Boughside Wanderers: the player chooses a permanent card among the top
four; the rest go to the bottom. -/
#guard
  let g := addToLibraryTop (addToLibraryTop (addToLibraryTop afterDraw shock me) grizzlyBears me) hillGiant me
  let g := addPermanent g boughsideWanderers me me
  let g := passBoth (fireTrigger g "Boughside Wanderers")
  let bears := (g.player me).library.find? (fun id => (g.object! id).name == "Grizzly Bears")
  let shockId := (g.player me).library.find? (fun id => (g.object! id).name == "Shock")
  let rejected := match shockId with
    | some id => (match g.apply me (.choosePermanents #[id]) with | .error _ => true | .ok _ => false)
    | none => false
  let g := mustApply g me (.choosePermanents #[bears.getD ⟨0⟩])
  rejected && inHand g me "Grizzly Bears" &&
    ((g.player me).library[0]?.any (fun id => ["Shock", "Hill Giant"].contains (g.object! id).name) ||
     (g.player me).library[1]?.any (fun id => ["Shock", "Hill Giant"].contains (g.object! id).name))

/- Gandalf, Goblins' Bane deals damage (not life loss) to each opponent. -/
#guard
  let g := fireTrigger (addPermanent afterDraw gandalfGoblinsBane me me) "Gandalf, Goblins' Bane"
  let g := passBoth g
  life g opp == 19 && (g.player opp).dealtNoncombatDamageThisTurn

/- The Black Arrow destroys a Dragon it damaged, but not another creature. -/
#guard
  let g := addPermanent (addPermanent afterDraw theBlackArrow me me) smaugWickedWorm opp opp
  let g := fireTrigger g "The Black Arrow"
  let g := passBoth (mustApply g me (.target (.permanent (theirs g "Smaug, Wicked Worm").id)))
  !g.objects.any (fun o => o.name == "Smaug, Wicked Worm" && o.isOnBattlefield)
#guard
  let g := addPermanent (addPermanent afterDraw theBlackArrow me me) hillGiant opp opp
  let g := fireTrigger g "The Black Arrow"
  let g := passBoth (mustApply g me (.target (.permanent (theirs g "Hill Giant").id)))
  (theirs g "Hill Giant").isOnBattlefield

/-! ## Life loss -/

/- The Master of Lake-town: damage and paying life are losses of life; that
player mills that many. -/
#guard
  let g := addPermanent afterDraw theMasterOfLakeTown me me
  let lib := (g.player opp).library.size
  let g := settle (castFra g lightningBolt [.target (.player opp)])
  (g.player opp).library.size == lib - 3
#guard
  let g := addPermanent (addPermanent afterDraw theMasterOfLakeTown me me) mountDoom me me
  let lib := (g.player me).library.size
  let g := settle (tapFor g "Mount Doom" (.colored .black))
  (g.player me).library.size == lib - 1

/-! ## Damage sources -/

/- Hawkeye, Young Avenger adds his power to noncombat damage a source you
control deals to an opponent, here from Stone-Giant's activated ability. -/
#guard
  let g := addPermanent (addPermanent afterDraw hawkeyeYoungAvenger me me) stoneGiantOfHighPass me me
  let g := addPermanent g murmuringVolume me me
  let g := activateNamed g "Stone-Giant of High Pass" "4 damage" [.target (.player opp)]
  let g := resolved (pick g #[idOf g "Murmuring Volume"])
  life g opp == 20 - 4 - power g "Hawkeye, Young Avenger"
/- It doesn't add to damage dealt to your own permanents. -/
#guard
  let g := addPermanent (addPermanent afterDraw hawkeyeYoungAvenger me me) crawWurm me me
  let g := resolved (castFra g shock [tgt g "Craw Wurm"])
  (namedPermanent g "Craw Wurm").status.damage == 2

/-! ## Copies -/

/- Photon Blast Barrage copies itself X times when cast; each copy may get a
new target. -/
#guard
  let g := addPermanent (addPermanent afterDraw grizzlyBears opp opp) hillGiant opp opp
  let g := castFra g photonBlastBarrage [.chooseX 2, tgt g "Grizzly Bears"]
  let g := passBoth g
  let offered := match g.pending with
    | .fraChoice _ (.newTargetsForCopies cs) => cs.size == 2
    | _ => false
  let g := mustApply g me (.choosePermanents #[(theirs g "Hill Giant").id])
  let g := settle (mustApply g me .decline)
  offered && !onBattlefield g "Grizzly Bears" && (theirs g "Hill Giant").status.damage == 1

/-! ## Flashback -/

/- A countered flashback spell is exiled instead of going to the graveyard
(CR 702.34a). -/
#guard
  let g := everyColor (addToGraveyard afterDraw tidingsOfWar me) me
  let g := mustApply g me (.cast (graveyardObj g me "Tidings of War").id)
  let g := mustApply g me .pay
  let spell := (g.stack.back?.map (·.objectId)).getD ⟨0⟩
  let g := g.counterStackSpell spell
  inExile g "Tidings of War" && !inGraveyard g me "Tidings of War"

/-! ## Kicker changes targets -/

/- The Eagles Are Coming! targets a creature you own, even one an opponent
controls; kicked, it targets any number of them. -/
#guard
  let g := addPermanent (addPermanent afterDraw grizzlyBears me opp) hillGiant opp me
  let g := resolved (castFra g theEaglesAreComing [.announceKicker false, tgt g "Grizzly Bears"])
  inHand g me "Grizzly Bears" && (g.player me).eaglesBirdsNextUpkeep == 1
#guard
  let g := addPermanent (addPermanent afterDraw grizzlyBears me opp) hillGiant opp me
  castRejected g theEaglesAreComing [.announceKicker false, tgt g "Hill Giant"]
#guard
  let g := addPermanent (addPermanent afterDraw grizzlyBears me me) hillGiant me me
  let g := resolved (castFra g theEaglesAreComing
    [.announceKicker true, .targets #[perm g "Grizzly Bears", perm g "Hill Giant"]])
  inHand g me "Grizzly Bears" && inHand g me "Hill Giant" && (g.player me).eaglesBirdsNextUpkeep == 2

/- Galadriel's Dismissal kicked targets a player, and each creature that
player controls phases out. -/
#guard
  let g := addPermanent (addPermanent afterDraw grizzlyBears opp opp) hillGiant opp opp
  let g := resolved (castFra g galadrielSDismissal [.announceKicker true, .target (.player opp)])
  let phased (n : String) := g.objects.any (fun o => o.name == n && o.zone == .battlefield && o.status.phasedOut)
  phased "Grizzly Bears" && phased "Hill Giant"

def shuffledSince (before : Nat) (g : Game) : Bool :=
  (g.log.extract before g.log.size).any (fun s => mentions s "shuffles")

def onlyLib (g : Game) (cards : Array CardDef) : Game :=
  let g := g.modifyPlayer me (fun pl => { pl with library := #[] })
  cards.foldl (fun g c => addToLibraryTop g c me) g

/- A library search is the player's choice. Declining finds nothing and still
shuffles; Old Thrush's optional search does not shuffle when declined. -/
#guard
  let g0 := addToLibraryTop afterDraw forest me
  let n := g0.log.size
  let g := g0.beginLibrarySearch me isBasicLandCard "a basic land card" .topAfterShuffle
    (optional := true)
  let g := mustApply g me .decline
  !shuffledSince n g &&
    (g.player me).library.any (fun id => (g.object! id).name == "Forest") &&
    g.log.any (fun s => mentions s "doesn't search")
#guard
  let g := addToLibraryTop afterDraw forest me
  let fid := (g.player me).library.back!
  let g := g.beginLibrarySearch me isBasicLandCard "a basic land card" .topAfterShuffle
    (optional := true)
  let g := mustApply g me .accept
  let g := mustApply g me (.choosePermanents #[fid])
  (g.player me).library.back? == some fid &&
    g.log.any (fun s => mentions s "on top of their library")

/- Troop of Ponies: the first chosen basic enters tapped, the second goes to hand. -/
#guard
  let g := onlyLib afterDraw #[plains, forest]
  let g := applyIdle (g.applyAbilityEffect me Effect.searchTwoBasicsSplit #[])
  let plainsBf := g.battlefield.any (fun o => o.name == "Plains" && o.status.tapped)
  plainsBf && inHand g me "Forest"

/- Elven Passage untaps the found land only when an Elf is beheld. -/
#guard
  let g := onlyLib afterDraw #[forest]
  let g := applyIdle (g.applyAbilityEffect me Effect.searchBasicBeholdElfUntap #[])
  (namedPermanent g "Forest").status.tapped &&
    g.log.any (fun s => mentions s "does not behold")
#guard
  let g := addPermanent afterDraw llanowarElves me me
  let g := onlyLib g #[forest]
  let g := applyIdle (g.applyAbilityEffect me Effect.searchBasicBeholdElfUntap #[])
  !(namedPermanent g "Forest").status.tapped &&
    g.log.any (fun s => mentions s "beholds a Elf")

/- Last Light shuffles only when the Dragon comes from the library. -/
#guard
  let g0 := addToHand afterDraw smaugWickedWorm me
  let n := g0.log.size
  let g := g0.beginLibrarySearch me (fun c => c.hasSubtype "Dragon") "a Dragon card"
    .battlefieldFromHandOrLibrary (alsoHand := true)
  let g := mustApply g me (.choosePermanents #[(handObj g me "Smaug, Wicked Worm").id])
  onBattlefield g "Smaug, Wicked Worm" && !shuffledSince n g
#guard
  let g0 := onlyLib afterDraw #[smaugWickedWorm]
  let n := g0.log.size
  let g := applyIdle (g0.beginLibrarySearch me (fun c => c.hasSubtype "Dragon") "a Dragon card"
    .battlefieldFromHandOrLibrary (alsoHand := true))
  onBattlefield g "Smaug, Wicked Worm" && shuffledSince n g

/- Outside the declare blockers step, sneak can't be used. -/
#guard
  let g := addPermanent afterDraw grizzlyBears me me
  let g := withMana (addToHand g elektraDaughterOfTheHand me) me .black 3
  match g.apply me (.castWithSneak (handObj g me "Elektra, Daughter of the Hand").id
      (idOf g "Grizzly Bears")) with
  | .error _ => true
  | .ok _ => false

end Mtg.Engine.CatalogModelTests
