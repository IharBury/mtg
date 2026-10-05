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

end Mtg.Engine.CatalogModelTests
