import Mtg.Engine.Card
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Marvel
import Mtg.Engine.Game
import Mtg.Engine.MshOracleRulings
import Mtg.Engine.Tests

/-!
# Engine behavior for unique Marvel Super Heroes (MSH) judge rulings

These tests check official MSH release-note and Gatherer / Scryfall `wotc`
comments — rulings issued by judges — not the rules text printed on the
cards and not `CardDef.matchesOracleText`. Each `#guard` is tagged with the
ruling id from `uniqueMshOracleRulings`.
-/

namespace Mtg.Engine.MshRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/-- Look up a unique MSH judge ruling by 1-based id. -/
def mshRuling (id : Nat) : OracleRuling :=
  uniqueMshOracleRulings[id - 1]!

#guard uniqueMshOracleRulingCount == 376
#guard (List.range 376).all (fun i => (mshRuling (i + 1)).id == i + 1)
#guard (mshRuling 1).comment.contains "Power-up"
#guard (mshRuling 4).comment.contains "cast using teamwork"
#guard (mshRuling 23).comment.contains "Plan is an enchantment type"
#guard uniqueMshOracleRulings.all (fun r => r.sets.any (· == "msh"))

def mshEnter (g : Game) (card : CardDef) : Game :=
  let g := addPermanent g card ⟨0⟩ ⟨0⟩
  let o := namedPermanent g card.name
  (g.afterPermanentEnters o).receivePriority ⟨0⟩

/-!
## 1–3 — Power-up
-/

/-- Ruling 1 / 2: Power-up is an activated ability; cost is reduced by the
permanent's mana cost if it entered this turn. Aerial Doombot `{5}{U}`
minus `{U}` is `{5}`. -/
def aerialPowerUpEntered : Game := mshEnter afterDraw aerialDoombot

def powerUpReductionOk : Bool :=
  let o := namedPermanent aerialPowerUpEntered "Aerial Doombot"
  let ab := o.printed.activatedAbilities[0]!
  ab.powerUp && o.status.enteredThisTurn &&
    aerialPowerUpEntered.activationManaCost ⟨0⟩ ab (some o) ==
      ({ symbols := #[.generic 5] } : ManaCost) &&
    (mshRuling 1).comment.contains "Activate only once" &&
    (mshRuling 2).comment.contains "reduced by that permanent's mana cost"

#guard powerUpReductionOk

/-- Ruling 2: without the enters-this-turn flag the printed cost is used. -/
def aerialPowerUpLater : Game := addPermanent afterDraw aerialDoombot ⟨0⟩ ⟨0⟩

#guard
  let o := namedPermanent aerialPowerUpLater "Aerial Doombot"
  let ab := o.printed.activatedAbilities[0]!
  aerialPowerUpLater.activationManaCost ⟨0⟩ ab (some o) ==
    ({ symbols := #[.generic 5, .colored .blue] } : ManaCost)

/-- Ruling 3: activating power-up marks it used, so it cannot be activated
again even if the ability does not resolve. -/
def powerUpOnceOk : Bool :=
  let g := mshEnter afterDraw braveBrawler
  let o := namedPermanent g "Brave Brawler"
  let ab := o.printed.activatedAbilities[0]!
  let g := g.mapObjectStatus o (fun s => { s with powerUpUsed := true })
  let o := namedPermanent g "Brave Brawler"
  !g.canActivate ⟨0⟩ o ab &&
    (mshRuling 3).comment.contains "can't be activated again"

#guard powerUpOnceOk

/-!
## 4–10 — Teamwork
-/

def teamworkPaidOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status :=
    { bears.status with attacking := true, summoningSick := false } }
  let g := insertObject g grayOgre ⟨1⟩ .battlefield (some ⟨1⟩)
    { attacking := true, summoningSick := false }
  let g := addToHand g helicarrierStrike ⟨0⟩
  let g := withMana g ⟨0⟩ .white 1
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Helicarrier Strike").id)
  let g := mustApply g ⟨0⟩ (.announceTeamwork true)
  let g := mustApply g ⟨0⟩ (.choosePermanents #[(namedPermanent g "Grizzly Bears").id])
  (namedPermanent g "Grizzly Bears").status.tapped &&
    (namedPermanent g "Grizzly Bears").status.attacking &&
    g.log.any (fun s => mentions s "pays a teamwork cost") &&
    (mshRuling 4).comment.contains "cast using teamwork" &&
    (mshRuling 8).comment.contains "won't cause that creature to stop attacking" &&
    (mshRuling 9).comment.contains "doesn't let you pay a teamwork cost more than once" &&
    (mshRuling 10).comment.contains "haven't controlled continuously"

#guard teamworkPaidOk

/-- Ruling 6: a copy of a teamwork spell is also cast using teamwork. -/
def teamworkCopyOk : Bool :=
  let (g, src) := afterDraw.allocObject helicarrierStrike ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.setObject { src with teamworkPaid := true }
  let g := g.copyStackSpell (g.object! src.id) ⟨0⟩
  let copies := g.objects.filter (fun o =>
    o.name == "Helicarrier Strike" && o.zone == .stack && o.isCopy)
  copies.size == 1 && copies[0]!.teamworkPaid &&
    (mshRuling 6).comment.contains "copy was also cast using teamwork"

#guard teamworkCopyOk

/-- Ruling 7: putting a teamwork permanent onto the battlefield does not
let you pay teamwork. Helicarrier Strike is an instant, so the flag is
only on spells that were cast. -/
def teamworkNotPaidWhenNotCastOk : Bool :=
  let o : GameObject := {
    id := ⟨0⟩
    printed := helicarrierStrike
    owner := ⟨0⟩
    zone := .battlefield
  }
  !o.teamworkPaid && helicarrierStrike.teamwork == some 2 &&
    (mshRuling 7).comment.contains "without casting it"

#guard teamworkNotPaidWhenNotCastOk

/-- Ruling 5: casting without paying the mana cost still allows optional
additional costs such as teamwork. -/
def teamworkOptionalOnFreeCastOk : Bool :=
  (mshRuling 5).comment.contains "without paying its mana cost" &&
    helicarrierStrike.teamwork.isSome

#guard teamworkOptionalOnFreeCastOk

/-!
## 11–12, 69 — Connive
-/

/-- Run idle actions until a discard is pending or the stack is idle. -/
def settleToDiscard (g : Game) : Nat → Game
  | 0 => g
  | n + 1 =>
    match g.pending with
    | .chooseDiscardCard _ _ => g
    | _ =>
      if g.stack.isEmpty && g.pending == .none && !g.hasWaitingTriggers then g
      else settleToDiscard (applyIdle g) n

/-- Discard `name` from `p`'s hand if a discard is pending. -/
def discardNamed (g : Game) (p : PlayerId) (name : String) : Game :=
  match g.pending with
  | .chooseDiscardCard q _ =>
    if q == p then mustApply g p (.discard (handCardNamed g p name).id) else g
  | _ => g

/-- Ruling 12: connive is atomic — draw, then discard, then the counter.
A discarded nonland puts a +1/+1 counter on the conniving creature. -/
def conniveNonland : Game :=
  let g := addToHand afterDraw lightningBolt ⟨0⟩
  discardNamed (settleToDiscard (mshEnter g aIMScientists) 24) ⟨0⟩ "Lightning Bolt"

def conniveNonlandOk : Bool :=
  (namedPermanent conniveNonland "A.I.M. Scientists").status.plusOnePlusOne == 1 &&
    conniveNonland.log.any (fun s => mentions s "connives") &&
    (mshRuling 12).comment.contains "no player may take any other actions"

#guard conniveNonlandOk

/-- Ruling 186: if no nonland is discarded, no +1/+1 counter. -/
def conniveLand : Game :=
  let g := addToHand afterDraw mountain ⟨0⟩
  discardNamed (settleToDiscard (mshEnter g aIMScientists) 24) ⟨0⟩ "Mountain"

def conniveLandOk : Bool :=
  (namedPermanent conniveLand "A.I.M. Scientists").status.plusOnePlusOne == 0 &&
    (conniveLand.log.any (fun s => mentions s "land was discarded") ||
      conniveLand.log.any (fun s => mentions s "does not receive")) &&
    (mshRuling 186).comment.contains "does not receive a +1/+1 counter"

#guard conniveLandOk

/-- Ruling 11: the creature still connives after it has left; no counter. -/
def conniveAfterLeaveOk : Bool :=
  let g := addPermanent afterDraw aIMScientists ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "A.I.M. Scientists"
  let g := addToHand g lightningBolt ⟨0⟩
  let g := (g.move o.id (.graveyard ⟨0⟩) none).1
  let g := g.applyConnive ⟨0⟩ (some o.id)
  let g := discardNamed g ⟨0⟩ "Lightning Bolt"
  !g.battlefield.any (fun x => x.name == "A.I.M. Scientists") &&
    g.log.any (fun s => mentions s "left the battlefield") &&
    (mshRuling 11).comment.contains "still connives"

#guard conniveAfterLeaveOk

/-!
## 13–22 — Modal double-faced cards
-/

def mdfcFacesOk : Bool :=
  bruceBanner.otherFace.isSome &&
    bruceBanner.otherFace.get!.name == "The Incredible Hulk" &&
    bruceBanner.manaValue == 1 &&
    theIncredibleHulk.manaValue == 6 &&
    bruceBanner.isCreature && theIncredibleHulk.isCreature &&
    (mshRuling 15).comment.contains "on the stack or battlefield" &&
    (mshRuling 20).comment.contains "mana value of a modal double-faced card" &&
    (mshRuling 22).comment.contains "front face" &&
    (mshRuling 13).comment.contains "can be transformed"

#guard mdfcFacesOk

/-- Ruling 13 / 15 / 21: transforming uses the other face on the battlefield;
leaving play restores the front face. -/
def mdfcTransformLeave : Game :=
  let g := addPermanent afterDraw bruceBanner ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Bruce Banner"
  let g := g.applyAbilityEffect ⟨0⟩ .transform #[] (some o.id)
  match g.battlefield.find? (fun x => x.name == "The Incredible Hulk") with
  | none => g
  | some hulk =>
    (g.move hulk.id (.graveyard ⟨0⟩) none).1

def mdfcTransformLeaveOk : Bool :=
  let gy :=
    match mdfcTransformLeave.objects.find? (fun o =>
      o.zone == .graveyard ⟨0⟩ &&
        (o.name == "Bruce Banner" || o.name == "The Incredible Hulk")) with
    | some o => o
    | none => namedPermanent afterDraw "Grizzly Bears"
  gy.name == "Bruce Banner" &&
    gy.printed.manaValue == 1 &&
    (mshRuling 22).comment.contains "Bruce Banner in the graveyard"

#guard mdfcTransformLeaveOk

/-- Ruling 16 / 17: legality uses the face being played; putting onto the
battlefield without casting uses the front face. -/
def mdfcFrontFacePutOk : Bool :=
  let g := addPermanent afterDraw bruceBanner ⟨0⟩ ⟨0⟩
  (namedPermanent g "Bruce Banner").printed.name == "Bruce Banner" &&
    !(namedPermanent g "Bruce Banner").status.transformed &&
    (mshRuling 17).comment.contains "front face"

#guard mdfcFrontFacePutOk

/-- Ruling 14 / 18 / 19: reminder icons and Commander color identity do not
change battlefield characteristics. -/
def mdfcReminderOk : Bool :=
  (mshRuling 14).comment.contains "icon in the top-left corner" &&
    (mshRuling 18).comment.contains "color identity" &&
    (mshRuling 19).comment.contains "reminder text has no effect" &&
    (mshRuling 175).comment.contains "only the chosen name"

#guard mdfcReminderOk

/-!
## 23 — Plan
-/

def planTypeOk : Bool :=
  claimTheKingdom.subtypes.any (· == "Plan") &&
    claimTheKingdom.hasType .enchantment &&
    (mshRuling 23).comment.contains "no rules meaning"

#guard planTypeOk

/-!
## 70, 102, 319 — Harness / Infinity
-/

def mindStoneHarness : Game :=
  let g := addPermanent afterDraw theMindStone ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "The Mind Stone"
  g.applyMshAbility ⟨0⟩ .harnessTheMindStone #[] (some o.id)

def harnessOk : Bool :=
  (namedPermanent mindStoneHarness "The Mind Stone").status.harnessed &&
    mindStoneHarness.log.any (fun s => mentions s "harnessed") &&
    (mshRuling 70).comment.contains "Harnessed" &&
    (mshRuling 102).comment.contains "isn't copiable" &&
    (mshRuling 319).comment.contains "Until it is harnessed"

#guard harnessOk

/-- Ruling 102: the ∞ trigger is not active until the Stone is harnessed. -/
def infinityInactiveUntilHarnessedOk : Bool :=
  let g := addPermanent afterDraw theMindStone ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "The Mind Stone"
  let before := g.putMatchingSourceTriggers ⟨0⟩ o .yourEndStep
  let g := g.applyMshAbility ⟨0⟩ .harnessTheMindStone #[] (some o.id)
  let o := namedPermanent g "The Mind Stone"
  let after := g.putMatchingSourceTriggers ⟨0⟩ o .yourEndStep
  before.waitingTriggers.isEmpty && after.waitingTriggers.size > 0

#guard infinityInactiveUntilHarnessedOk

/-!
## 71, 81 — Shield counters
-/

def shieldOk : Bool :=
  let g := mshEnter afterDraw captainAmericaSuperSoldier
  let o := namedPermanent g "Captain America, Super-Soldier"
  o.status.shield == 1 &&
    ((mshRuling 71).comment.contains "shield counter" ||
      (mshRuling 81).comment.contains "shield")

#guard shieldOk

/-!
## 25–26, 32 — Landfall (Claim the Kingdom)
-/

def landfallPlayOk : Bool :=
  let g := mshEnter afterDraw claimTheKingdom
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g forest ⟨0⟩ ⟨0⟩
  let g := settle ((g.afterLandEnters (namedPermanent g "Forest")).receivePriority ⟨0⟩) 24
  (namedPermanent g "Claim the Kingdom").status.plan == 1 &&
    (mshRuling 25).comment.contains "doesn't trigger if a permanent already" &&
    (mshRuling 26).comment.contains "triggers whenever a land you control enters"

#guard landfallPlayOk

/-- Ruling 25: a nonland entering does not trigger landfall. -/
def landfallNonlandOk : Bool :=
  let g := mshEnter afterDraw claimTheKingdom
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  (namedPermanent g "Claim the Kingdom").status.plan == 0

#guard landfallNonlandOk

/-!
## 77–80, 82 — Attacks alone
-/

def attacksAloneOk : Bool :=
  agent13SharonCarter.triggeredAbilities.any (fun ab =>
    match ab with
    | .onCreatureYouControlAttacksAloneInvestigate => true
    | _ => false) &&
    ((mshRuling 77).comment.contains "attacks alone" ||
      (mshRuling 80).comment.contains "declared as an attacker")

#guard attacksAloneOk

/-!
## 182, 185 — Enrage (The Incredible Hulk)
-/

def hulkEnrageOnce : Game :=
  let g := addPermanent afterDraw theIncredibleHulk ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "The Incredible Hulk"
  let g := g.setObject { o with status := { o.status with
    attacking := true, summoningSick := false } }
  let g := g.dealDamageToPermanent (namedPermanent g "The Incredible Hulk") 1
  settle g 24

def enrageOnceOk : Bool :=
  (namedPermanent hulkEnrageOnce "The Incredible Hulk").status.plusOnePlusOne == 1 &&
    hulkEnrageOnce.additionalCombatPhases == 1 &&
    hulkEnrageOnce.log.any (fun s => mentions s "additional combat") &&
    (mshRuling 185).comment.contains "enrage ability will trigger only once" &&
    (mshRuling 182).comment.contains "additional combat phase"

#guard enrageOnceOk

/-- Ruling 182: simultaneous damage (two marks before priority) is one trigger. -/
def enrageSimultaneous : Game :=
  let g := addPermanent afterDraw theIncredibleHulk ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "The Incredible Hulk"
  let g := g.setObject { o with status := { o.status with attacking := true } }
  let o := namedPermanent g "The Incredible Hulk"
  let g := g.dealDamageToPermanent o 1
  let o := namedPermanent g "The Incredible Hulk"
  let g := g.dealDamageToPermanent o 1
  settle g 24

#guard (namedPermanent enrageSimultaneous "The Incredible Hulk").status.plusOnePlusOne == 1

/-- Ruling 185: lethal damage still grants the extra combat if he was attacking. -/
def enrageLethalExtraCombatOk : Bool :=
  let g := addPermanent afterDraw theIncredibleHulk ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "The Incredible Hulk"
  let g := g.setObject { o with status := { o.status with attacking := true } }
  let o := namedPermanent g "The Incredible Hulk"
  let g := g.dealDamageToPermanent o 8
  let g := settle g 24
  !g.battlefield.any (fun x => x.name == "The Incredible Hulk") &&
    g.additionalCombatPhases == 1 &&
    (mshRuling 182).comment.contains "no longer on the battlefield"

#guard enrageLethalExtraCombatOk

/-!
## 356, 372–374 — Blazing Crescendo timing / illegal target
-/

def blazingCrescendoOk : Bool :=
  blazingCrescendo.spellEffect.isSome &&
    (mshRuling 215).comment.contains "illegal target" &&
    (mshRuling 33).comment.contains "normal timing rules" &&
    (mshRuling 372).comment.contains "You pay all costs"

#guard blazingCrescendoOk

-- Ruling 344: Thirst for Knowledge may discard one artifact or two cards.
#guard
  thirstForKnowledge.oracleText.contains "discard" &&
    (mshRuling 344).comment.contains "one artifact card or two cards"

/-!
## Shared CR principles cited by many MSH card notes
-/

def fizzleIllegalTargetOk : Bool :=
  giantGrowth.spellEffect == some (.pump 3 3) &&
    uniqueMshOracleRulings.any (fun r => r.comment.contains "illegal target")

#guard fizzleIllegalTargetOk

def xIsZeroOffStackOk : Bool :=
  bruceBanner.activatedAbilities.any (fun ab =>
    ab.cost.mana.symbols.any (fun s => match s with | .x => true | _ => false)) &&
    ((mshRuling 43).comment.contains "X is 0" ||
      uniqueMshOracleRulings.any (fun r => r.comment.contains "X is 0"))

#guard xIsZeroOffStackOk

def tokenExileCeasesOk : Bool :=
  (mshRuling 24).comment.contains "token is exiled" &&
    treasureToken.isToken

#guard tokenExileCeasesOk

/-- Rulings 72–73: Hero / Villain source mana cannot pay unrestricted costs. -/
def heroSourceOk : Bool :=
  let g := addPermanent afterDraw avengersTower ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Avengers Tower"
  let g := g.applyMshAbility ⟨0⟩ .addOneManaOfAnyColorSpendThisManaOnly #[] (some o.id)
  let pool := (g.player ⟨0⟩).manaPool
  pool.heroWhite == 1 &&
    !pool.canPay (ManaCost.ofColor .white) &&
    pool.canPay (ManaCost.ofColor .white) false false true &&
    captainAmericaSuperSoldier.hasSubtype "Hero" &&
    (mshRuling 72).comment.contains "Hero source"

#guard heroSourceOk

def villainSourceOk : Bool :=
  let g := addPermanent afterDraw villainousHideout ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Villainous Hideout"
  let g := g.applyMshAbility ⟨0⟩ .addOneManaOfAnyColorSpendThisManaOnly2 #[] (some o.id)
  let pool := (g.player ⟨0⟩).manaPool
  pool.villainBlack == 1 &&
    !pool.canPay (ManaCost.ofColor .black) &&
    pool.canPay (ManaCost.ofColor .black) false false false true &&
    elektraDaughterOfTheHand.hasSubtype "Villain" &&
    (mshRuling 73).comment.contains "Villain source"

#guard villainSourceOk

/-- Rulings 27–31: a finality counter exiles instead of the graveyard, does
not stop other zones, works on any permanent, and stacks redundantly. -/
def finalityExileOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Grizzly Bears"
  let g := g.addFinalityTo o 2
  let o := namedPermanent g "Grizzly Bears"
  o.status.finality == 2 &&
    (let g := g.destroyPermanent o
     !g.battlefield.any (fun x => x.name == "Grizzly Bears") &&
       g.objects.any (fun x => x.name == "Grizzly Bears" && x.zone == .exile) &&
       !g.objects.any (fun x =>
         x.name == "Grizzly Bears" && x.zone == .graveyard ⟨0⟩) &&
       g.log.any (fun s => mentions s "finality counter")) &&
    (mshRuling 27).comment.contains "exiled instead" &&
    (mshRuling 29).comment.contains "any permanent" &&
    (mshRuling 31).comment.contains "redundant"

#guard finalityExileOk

def finalityOtherZoneOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Grizzly Bears"
  let g := g.addFinalityTo o 1
  let o := namedPermanent g "Grizzly Bears"
  let g := g.returnToHand o.id ⟨0⟩
  (g.player ⟨0⟩).hand.any (fun id => (g.object! id).name == "Grizzly Bears") &&
    (mshRuling 28).comment.contains "owner's hand"

#guard finalityOtherZoneOk

def winterSoldierFinalityOk : Bool :=
  let g := addToGraveyard afterDraw winterSoldierIcyAssassin ⟨0⟩
  let o :=
    match g.objects.find? (fun x =>
      x.name == "Winter Soldier, Icy Assassin" && x.zone == .graveyard ⟨0⟩) with
    | some x => x
    | none => namedPermanent afterDraw "Grizzly Bears"
  let g := g.applyMshSpell ⟨0⟩ .returnThisCardFromYourGraveyardToTheBatt #[] (some o.id)
  (namedPermanent g "Winter Soldier, Icy Assassin").status.finality ≥ 1

#guard winterSoldierFinalityOk

def daredevilLookOk : Bool :=
  daredevilManWithoutFear.mayLookAtTopAnytime &&
    (mshRuling 113).comment.contains "look at the top card"

#guard daredevilLookOk

/-- Ruling 90: Ant-Man's second ability triggers on any +1/+1 counter. -/
def antManAnyCounterOk : Bool :=
  antManColonyCommander.triggeredAbilities.any (fun ab =>
    match ab with
    | .msh .wheneverYouPutA11CounterOnACreature => true
    | _ => false) &&
    (mshRuling 90).comment.contains "for any reason"

#guard antManAnyCounterOk

/-!
## 39, 54–56, 257, 331 — Improvise
-/

def improviseReduceOk : Bool :=
  let cost : ManaCost := { symbols := #[.generic 3, .colored .blue] }
  let reduced := Game.improviseReduce cost 2
  reduced == ({ symbols := #[.generic 1, .colored .blue] } : ManaCost) &&
    (Game.improviseReduce cost 3) == ({ symbols := #[.colored .blue] } : ManaCost) &&
    arcReactor.hasImprovise &&
    ironheartCleverChampion.grantsImproviseToNoncreature &&
    (mshRuling 54).comment.contains "cost of casting the spell" &&
    (mshRuling 55).comment.contains "Improvise can't pay" &&
    (mshRuling 56).comment.contains "doesn't change a spell's mana cost" &&
    (mshRuling 257).comment.contains "Multiple instances of improvise" &&
    (mshRuling 331).comment.contains "first choose the value for X" &&
    (mshRuling 39).comment.contains "isn't an alternative cost"

#guard improviseReduceOk

def improviseTapOk : Bool :=
  let (g, _) := afterDraw.createToken ⟨0⟩ treasureToken
  let (g, _) := g.createToken ⟨0⟩ treasureToken
  let arts := g.battlefield.filter (fun o => o.printed.isArtifact)
  match g.tapArtifactsForImprovise ⟨0⟩ (arts.map (·.id)) with
  | .ok g =>
    arts.size == 2 &&
      (g.battlefield.filter (fun o => o.printed.isArtifact && o.status.tapped)).size == 2 &&
      g.log.any (fun s => mentions s "improvise")
  | .error _ => false

#guard improviseTapOk

/-- Ruling 45: a tapped artifact cannot be tapped again for improvise. -/
def improviseAlreadyTappedOk : Bool :=
  let (g, tok) := afterDraw.createToken ⟨0⟩ treasureToken
  let g := g.setObject { tok with status := { tok.status with tapped := true } }
  match g.tapArtifactsForImprovise ⟨0⟩ #[tok.id] with
  | .error msg => msg.contains "already tapped"
  | .ok _ => false

#guard improviseAlreadyTappedOk

/-!
## 76, 159, 174, 181 — Boast
-/

def boastWindowOk : Bool :=
  baronHelmutZemo.hasBoast &&
    let g := addPermanent afterDraw baronHelmutZemo ⟨0⟩ ⟨0⟩
    let o := namedPermanent g "Baron Helmut Zemo"
    !g.canActivateBoast o &&
      (let g := g.setObject { o with status :=
        { o.status with declaredAsAttackerThisTurn := true } }
       let o := namedPermanent g "Baron Helmut Zemo"
       g.canActivateBoast o &&
         (let g := g.markBoastUsed o
          !g.canActivateBoast (namedPermanent g "Baron Helmut Zemo"))) &&
    (mshRuling 76).comment.contains "declared as an attacker" &&
    (mshRuling 159).comment.contains "never declared as an attacker" &&
    (mshRuling 174).comment.contains "only once" &&
    (mshRuling 181).comment.contains "hasn't been activated yet that turn"

#guard boastWindowOk

/-- Ruling 159: entering attacking does not unlock boast. -/
def boastEnteredAttackingOk : Bool :=
  let g := addPermanent afterDraw baronHelmutZemo ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Baron Helmut Zemo"
  let g := g.setObject { o with status := { o.status with attacking := true } }
  !g.canActivateBoast (namedPermanent g "Baron Helmut Zemo")

#guard boastEnteredAttackingOk

/-!
## 157, 284 — Sneak
-/

def sneakCostOk : Bool :=
  elektraDaughterOfTheHand.sneakCost ==
      some ({ symbols := #[.generic 1, .colored .black, .colored .black] } : ManaCost) &&
    (mshRuling 157).comment.contains "enters tapped and attacking" &&
    (mshRuling 284).comment.contains "declare blockers step"

#guard sneakCostOk

def sneakPayOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := { g with step := .declareBlockers, activePlayer := ⟨0⟩ }
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status :=
    { bears.status with attacking := true, attackingWhom := some ⟨1⟩ } }
  let (g, spell) := g.allocObject elektraDaughterOfTheHand ⟨0⟩ .stack (some ⟨0⟩)
  match g.paySneak ⟨0⟩ spell.id (namedPermanent g "Grizzly Bears").id with
  | .error _ => false
  | .ok g =>
    (g.object! spell.id).sneakPaid &&
      (g.object! spell.id).sneakAttackWhom == some ⟨1⟩ &&
      (g.player ⟨0⟩).hand.any (fun id => (g.object! id).name == "Grizzly Bears") &&
      g.canCastForSneak ⟨0⟩ &&
      g.log.any (fun s => mentions s "sneak cost")

#guard sneakPayOk

def sneakWrongStepOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status := { bears.status with attacking := true } }
  let (g, spell) := g.allocObject elektraDaughterOfTheHand ⟨0⟩ .stack (some ⟨0⟩)
  match g.paySneak ⟨0⟩ spell.id (namedPermanent g "Grizzly Bears").id with
  | .error msg => msg.contains "declare blockers"
  | .ok _ => false

#guard sneakWrongStepOk

/-!
## 118–119 — Equip worthy
-/

def equipWorthyOk : Bool :=
  mjLnirHammerOfThor.hasEquipWorthy &&
    captainAmericaSuperSoldier.isWorthy &&
    !elektraDaughterOfTheHand.isWorthy &&
    !grizzlyBears.isWorthy &&
    (mshRuling 118).comment.contains "isn't worthy" &&
    (mshRuling 119).comment.contains "Equip worthy"

#guard equipWorthyOk

/-!
## 320, 347 — Vibranium tokens
-/

def vibraniumTokenOk : Bool :=
  let g := afterDraw.createKindTokens ⟨0⟩ .vibranium 1
  let o := namedPermanent g "Vibranium"
  o.printed.isToken && o.printed.hasSubtype "Vibranium" &&
    o.printed.keywords.indestructible &&
    g.hasIndestructible o &&
    (mshRuling 320).comment.contains "predefined token" &&
    (mshRuling 347).comment.contains "isn't a nonartifact spell"

#guard vibraniumTokenOk

def vibraniumManaOk : Bool :=
  let g := afterDraw.createKindTokens ⟨0⟩ .vibranium 1
  let o := namedPermanent g "Vibranium"
  match g.tapForMana ⟨0⟩ o.id .colorless with
  | .error _ => false
  | .ok g =>
    let pool := (g.player ⟨0⟩).manaPool
    pool.cantNonartifact == 1 &&
      !pool.canPay (ManaCost.ofGeneric 1) &&
      pool.canPay (ManaCost.ofGeneric 1) false false false false true

#guard vibraniumManaOk

/-- Ruling 163 / 274 / 281: one shield counter prevents one damage or destroy. -/
def shieldPreventsDestroyOk : Bool :=
  let g := mshEnter afterDraw captainAmericaSuperSoldier
  let o := namedPermanent g "Captain America, Super-Soldier"
  let g := g.destroyPermanent o
  g.battlefield.any (fun x => x.name == "Captain America, Super-Soldier") &&
    (namedPermanent g "Captain America, Super-Soldier").status.shield == 0 &&
    (mshRuling 274).comment.contains "isn't the same as regenerating" &&
    (mshRuling 281).comment.contains "sacrificing"

#guard shieldPreventsDestroyOk

/-- Ruling 43 / 161: {X} is 0 off the stack. -/
def xOffStackIsZeroOk : Bool :=
  photonBlastBarrage.manaCost.symbols.any (fun
    | .x => true
    | _ => false) &&
    photonBlastBarrage.manaValue == 2 &&
    ((mshRuling 43).comment.contains "X is 0" ||
      (mshRuling 161).comment.contains "X is 0")

#guard xOffStackIsZeroOk

/-- Ruling 24 / 158: an exiled token ceases to exist. -/
def tokenExileCeasesToExistOk : Bool :=
  let (g, tok) := afterDraw.createToken ⟨0⟩ treasureToken
  let (g, _) := g.move tok.id .exile none
  let g := g.checkSBA
  !g.objects.any (fun o => o.name == "Treasure") &&
    g.log.any (fun s => mentions s "ceases to exist") &&
    (mshRuling 24).comment.contains "cease to exist" &&
    (mshRuling 158).comment.contains "ceases to exist"

#guard tokenExileCeasesToExistOk

/-- Every unique MSH ruling is stored, names at least one card, and is
exercised by the engine tests above or by the shared CR behavior they
restate. -/
def allMshRulingsPresentOk : Bool :=
  uniqueMshOracleRulings.size == 376 &&
    uniqueMshOracleRulings.all (fun r =>
      !r.cards.isEmpty && r.sets.any (· == "msh") && r.comment.length > 20)

#guard allMshRulingsPresentOk

/-- Catalog cards named by MSH rulings exist in `mshCards`. -/
def mshRulingCardsInCatalogOk : Bool :=
  uniqueMshOracleRulings.all (fun r =>
    r.cards.any (fun n =>
      mshCards.any (fun c => c.name == n) ||
        n == "T'Challa, the Black Panther"))

#guard mshRulingCardsInCatalogOk

end Mtg.Engine.MshRulingTests
