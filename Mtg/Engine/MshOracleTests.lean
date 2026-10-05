import Mtg.Engine.Card
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.OracleData
import Mtg.Engine.Tests.Abilities
import Mtg.Engine.Tests.Adventures
import Mtg.Engine.Tests.AttackTriggers
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Effects
import Mtg.Engine.Tests.Elves
import Mtg.Engine.Tests.Equipment
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Pathmaker
import Mtg.Engine.Tests.Removal
import Mtg.Engine.Tests.RulingFixtures
import Mtg.Engine.Tests.Turns


/-!
# Engine behavior for unique Marvel Super Heroes (MSH) judge rulings

These tests check official MSH release-note and Gatherer / Scryfall `wotc`
comments — rulings issued by judges — not the rules text printed on the
cards. Each `#guard` is tagged with the ruling id from `uniqueOracleRulings`.
Comments that also appear on HOB or HOC cards keep that shared id so the
same ruling applies across sets.

This module is the first slice of those checks. `Mtg.Engine.MshOracleTests2`
and `Mtg.Engine.MshOracleTests3` hold the rest, in `Mtg.Engine.MshRulingTests`,
so the slices compile in parallel.
-/

namespace Mtg.Engine.MshRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

#guard uniqueMshOracleRulingCount == 376
#guard uniqueOracleRulingCount == 893
#guard uniqueMshOracleRulings.all (fun r => (mshRuling r.id).id == r.id)
#guard (mshRuling 360).comment.contains "Power-up"
#guard (mshRuling 363).comment.contains "cast using teamwork"
#guard (mshRuling 382).comment.contains "Plan is an enchantment type"
#guard uniqueMshOracleRulings.all (fun r => r.sets.any (· == "msh"))

/-- Snapshot used to exercise `finishProposedSpell` restricted-mana payment. -/
def dummyProposal (g : Game) (kind : ProposalKind) (src : GameObject) (cost : ManaCost)
    (discardSource : Bool := false) : ProposedSpell :=
  { caster := ⟨0⟩
    cost
    spellId := src.id
    original := src
    handBefore := (g.player ⟨0⟩).hand
    stackBefore := g.stack
    manaBefore := (g.player ⟨0⟩).manaPool
    kind
    sourceId := if kind == .spell then none else some src.id
    discardSource }

/-- True when the proposed cost is paid (not reversed). -/
def paidOk (g : Game) (prop : ProposedSpell) : Bool :=
  let g := { g with proposedSpell := some prop }
  match g.finishProposedSpell with
  | .error _ => false
  | .ok g' => !g'.log.any (fun s => mentions s "reversed")

/-- True when the engine reverses the proposal for lack of payable mana. -/
def reversedPay (g : Game) (prop : ProposedSpell) : Bool :=
  let g := { g with proposedSpell := some prop }
  match g.finishProposedSpell with
  | .error _ => true
  | .ok g' => g'.log.any (fun s => mentions s "reversed")

def graveyardCardNamed (g : Game) (p : PlayerId) (name : String) : GameObject :=
  match g.objects.find? (fun o => o.name == name && o.zone == .graveyard p) with
  | some o => o
  | none => panic! s!"expected {name} in graveyard"

/-!
## 360–362 — Power-up
-/

/-- Ruling 360 / 2: Power-up is an activated ability; cost is reduced by the
permanent's mana cost if it entered this turn. Aerial Doombot `{5}{U}`
minus `{U}` is `{5}`. -/
def aerialPowerUpEntered : Game := mshEnter afterDraw aerialDoombot

def powerUpReductionOk : Bool :=
  let o := namedPermanent aerialPowerUpEntered "Aerial Doombot"
  let ab := o.printed.activatedAbilities[0]!
  ab.powerUp && o.status.enteredThisTurn &&
    aerialPowerUpEntered.activationManaCost ⟨0⟩ ab (some o) ==
      ({ symbols := #[.generic 5] } : ManaCost) &&
    (mshRuling 360).comment.contains "Activate only once" &&
    (mshRuling 361).comment.contains "reduced by that permanent's mana cost"

#guard powerUpReductionOk

/-- Ruling 361: without the enters-this-turn flag the printed cost is used. -/
def aerialPowerUpLater : Game := addPermanent afterDraw aerialDoombot ⟨0⟩ ⟨0⟩

#guard
  let o := namedPermanent aerialPowerUpLater "Aerial Doombot"
  let ab := o.printed.activatedAbilities[0]!
  aerialPowerUpLater.activationManaCost ⟨0⟩ ab (some o) ==
    ({ symbols := #[.generic 5, .colored .blue] } : ManaCost)

/-- Ruling 362: activating power-up marks it used, so it cannot be activated
again even if the ability does not resolve. -/
def powerUpOnceOk : Bool :=
  let g := mshEnter afterDraw braveBrawler
  let o := namedPermanent g "Brave Brawler"
  let ab := o.printed.activatedAbilities[0]!
  let g := g.mapObjectStatus o (fun s => { s with powerUpUsed := true })
  let o := namedPermanent g "Brave Brawler"
  !g.canActivate ⟨0⟩ o ab &&
    (mshRuling 362).comment.contains "can't be activated again"

#guard powerUpOnceOk

/-!
## 363–369 — Teamwork
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
    (mshRuling 363).comment.contains "cast using teamwork" &&
    (mshRuling 367).comment.contains "won't cause that creature to stop attacking" &&
    (mshRuling 368).comment.contains "doesn't let you pay a teamwork cost more than once" &&
    (mshRuling 369).comment.contains "haven't controlled continuously" &&
    (mshRuling 416).comment.contains "total cost of a spell" &&
    (mshRuling 418).comment.contains "additional costs" &&
    (mshRuling 665).comment.contains "total cost of a spell"

#guard teamworkPaidOk

/-- Ruling 365: a copy of a teamwork spell is also cast using teamwork. -/
def teamworkCopyOk : Bool :=
  let (g, src) := afterDraw.allocObject helicarrierStrike ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.setObject { src with teamworkPaid := true }
  let g := g.copyStackSpell (g.object! src.id) ⟨0⟩
  let copies := g.objects.filter (fun o =>
    o.name == "Helicarrier Strike" && o.zone == .stack && o.isCopy)
  copies.size == 1 && copies[0]!.teamworkPaid &&
    (mshRuling 365).comment.contains "copy was also cast using teamwork"

#guard teamworkCopyOk

/-- Ruling 366: putting a teamwork permanent onto the battlefield does not
let you pay teamwork. Helicarrier Strike is an instant, so the flag is
only on spells that were cast. -/
def teamworkNotPaidWhenNotCastOk : Bool :=
  let g := addPermanent afterDraw helicarrierStrike ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Helicarrier Strike"
  !o.teamworkPaid &&
    helicarrierStrike.teamwork == some 2 &&
    (match g.apply ⟨0⟩ (.announceTeamwork true) with
     | .error _ => true
     | .ok _ => false) &&
    (mshRuling 366).comment.contains "without casting it"

#guard teamworkNotPaidWhenNotCastOk

/-- Ruling 364: casting without paying the mana cost still allows optional
additional costs such as teamwork. -/
def teamworkOptionalOnFreeCastOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status :=
    { bears.status with attacking := true, summoningSick := false } }
  let g := addToHand g helicarrierStrike ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Helicarrier Strike"
  let g := g.setObject { card with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }
  let card := handCardNamed g ⟨0⟩ "Helicarrier Strike"
  !(g.playManaCost card helicarrierStrike).includesManaPayment &&
    (let g := mustApply g ⟨0⟩ (.cast card.id)
     let g := mustApply g ⟨0⟩ (.announceTeamwork true)
     let g := mustApply g ⟨0⟩ (.choosePermanents #[(namedPermanent g "Grizzly Bears").id])
     (namedPermanent g "Grizzly Bears").status.tapped &&
       g.log.any (fun s => mentions s "pays a teamwork cost")) &&
    (mshRuling 364).comment.contains "without paying its mana cost" &&
    helicarrierStrike.teamwork.isSome &&
    (mshRuling 582).comment.contains "teamwork costs"

#guard teamworkOptionalOnFreeCastOk

/-- Ruling 582: Titania's mandatory additional cost is still paid when the
spell is cast without paying its mana cost. -/
def titaniaFreeCastViaDiscard : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  let g := addToHand (addToHand g titaniaRuggedRumbler ⟨0⟩) forest ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Titania, Rugged Rumbler"
  let g := g.setObject { card with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }
  let g := mustApply g ⟨0⟩
    (.cast (handCardNamed g ⟨0⟩ "Titania, Rugged Rumbler").id)
  let g := mustApply g ⟨0⟩ (.chooseAdditionalCost false)
  let g := mustApply g ⟨0⟩ .pay
  mustApply g ⟨0⟩ (.discard (handCardNamed g ⟨0⟩ "Forest").id)

def titaniaMandatoryOnFreeCastOk : Bool :=
  titaniaFreeCastViaDiscard.log.any (fun s => mentions s "casts Titania") &&
    titaniaFreeCastViaDiscard.log.any (fun s =>
      mentions s "chooses to discard a card as an additional cost") &&
    (mshRuling 582).comment.contains "Titania, Rugged Rumbler"

#guard titaniaMandatoryOnFreeCastOk

/-!
## 370–371, 422 — Connive
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

/-- Ruling 371: connive is atomic — draw, then discard, then the counter.
A discarded nonland puts a +1/+1 counter on the conniving creature. -/
def conniveNonland : Game :=
  let g := addToHand afterDraw lightningBolt ⟨0⟩
  discardNamed (settleToDiscard (mshEnter g aIMScientists) 24) ⟨0⟩ "Lightning Bolt"

def conniveNonlandOk : Bool :=
  (namedPermanent conniveNonland "A.I.M. Scientists").status.plusOnePlusOne == 1 &&
    conniveNonland.log.any (fun s => mentions s "connives") &&
    (mshRuling 371).comment.contains "no player may take any other actions"

#guard conniveNonlandOk

/-- Ruling 538: if no nonland is discarded, no +1/+1 counter. -/
def conniveLand : Game :=
  let g := addToHand afterDraw mountain ⟨0⟩
  discardNamed (settleToDiscard (mshEnter g aIMScientists) 24) ⟨0⟩ "Mountain"

def conniveLandOk : Bool :=
  (namedPermanent conniveLand "A.I.M. Scientists").status.plusOnePlusOne == 0 &&
    (conniveLand.log.any (fun s => mentions s "land was discarded") ||
      conniveLand.log.any (fun s => mentions s "does not receive")) &&
    (mshRuling 538).comment.contains "does not receive a +1/+1 counter"

#guard conniveLandOk

/-- Ruling 370: the creature still connives after it has left; no counter. -/
def conniveAfterLeaveOk : Bool :=
  let g := addPermanent afterDraw aIMScientists ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "A.I.M. Scientists"
  let g := addToHand g lightningBolt ⟨0⟩
  let g := (g.move o.id (.graveyard ⟨0⟩) none).1
  let g := g.applyConnive ⟨0⟩ (some o.id)
  let g := discardNamed g ⟨0⟩ "Lightning Bolt"
  !g.battlefield.any (fun x => x.name == "A.I.M. Scientists") &&
    g.log.any (fun s => mentions s "left the battlefield") &&
    (mshRuling 370).comment.contains "still connives"

#guard conniveAfterLeaveOk

/-!
## 372–381 — Modal double-faced cards
-/

def mdfcFacesOk : Bool :=
  bruceBanner.otherFace.isSome &&
    bruceBanner.otherFace.get!.name == "The Incredible Hulk" &&
    bruceBanner.manaValue == 1 &&
    theIncredibleHulk.manaValue == 6 &&
    bruceBanner.isCreature && theIncredibleHulk.isCreature &&
    (let g := addPermanent afterDraw bruceBanner ⟨0⟩ ⟨0⟩
     let banner := namedPermanent g "Bruce Banner"
     g.objectManaValue banner == 1 &&
       (let g := g.applyAbilityEffect ⟨0⟩ (Effect.transform) #[] (some banner.id)
        g.objectManaValue (namedPermanent g "The Incredible Hulk") == 6)) &&
    (mshRuling 374).comment.contains "on the stack or battlefield" &&
    (mshRuling 379).comment.contains "mana value of a modal double-faced card" &&
    (mshRuling 381).comment.contains "front face" &&
    (mshRuling 372).comment.contains "can be transformed"

#guard mdfcFacesOk

/-- Ruling 372 / 15 / 21: transforming uses the other face on the battlefield;
leaving play restores the front face. -/
def mdfcTransformLeave : Game :=
  let g := addPermanent afterDraw bruceBanner ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Bruce Banner"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.transform) #[] (some o.id)
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
    (mshRuling 381).comment.contains "Bruce Banner in the graveyard"

#guard mdfcTransformLeaveOk

/-- Ruling 375 / 17: legality uses the face being played; putting onto the
battlefield without casting uses the front face. -/
def mdfcFrontFacePutOk : Bool :=
  let g := addPermanent afterDraw bruceBanner ⟨0⟩ ⟨0⟩
  let faces : Array CardDef :=
    match bruceBanner.otherFace with
    | none => #[bruceBanner]
    | some back => #[bruceBanner, back]
  let greenFaces :=
    faces.filter (fun c => c.colors.contains .green) |>.map (fun c => c.name)
  (namedPermanent g "Bruce Banner").printed.name == "Bruce Banner" &&
    !(namedPermanent g "Bruce Banner").status.transformed &&
    greenFaces == #["The Incredible Hulk"] &&
    (mshRuling 375).comment.contains "cast green spells" &&
    (mshRuling 376).comment.contains "front face"

#guard mdfcFrontFacePutOk

/-- Ruling 373 / 18 / 19: reminder icons have no rules; Commander color
identity of an MDFC is both faces combined, and that does not change the
front face's battlefield color. -/
def mdfcReminderOk : Bool :=
  let id := bruceBanner.colorIdentity
  bruceBanner.colors.contains .blue &&
    !bruceBanner.colors.contains .red &&
    !bruceBanner.colors.contains .green &&
    id.contains .blue &&
    id.contains .red &&
    id.contains .green &&
    !theIncredibleHulk.colors.contains .blue &&
    theIncredibleHulk.faceColorIdentity.contains .red &&
    theIncredibleHulk.faceColorIdentity.contains .green &&
    !theIncredibleHulk.faceColorIdentity.contains .blue &&
    (mshRuling 373).comment.contains "icon in the top-left corner" &&
    (mshRuling 377).comment.contains "color identity" &&
    (mshRuling 378).comment.contains "reminder text has no effect" &&
    (mshRuling 527).comment.contains "only the chosen name"

#guard mdfcReminderOk

/-!
## 382 — Plan
-/

def planTypeOk : Bool :=
  claimTheKingdom.subtypes.any (· == "Plan") &&
    claimTheKingdom.hasType .enchantment &&
    (mshRuling 382).comment.contains "no rules meaning"

#guard planTypeOk

/-!
## 423, 455, 671 — Harness / Infinity
-/

def mindStoneHarness : Game :=
  let g := addPermanent afterDraw theMindStone ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "The Mind Stone"
  g.applyAbilityEffect ⟨0⟩ (Effect.harnessInfinityStone) #[] (some o.id)

def harnessOk : Bool :=
  (namedPermanent mindStoneHarness "The Mind Stone").status.harnessed &&
    mindStoneHarness.log.any (fun s => mentions s "harnessed") &&
    (mshRuling 423).comment.contains "Harnessed" &&
    (mshRuling 455).comment.contains "isn't copiable" &&
    (mshRuling 671).comment.contains "Until it is harnessed"

#guard harnessOk

/-- Ruling 455: the ∞ trigger is not active until the Stone is harnessed. -/
def infinityInactiveUntilHarnessedOk : Bool :=
  let g := addPermanent afterDraw theMindStone ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "The Mind Stone"
  let before := g.putMatchingSourceTriggers ⟨0⟩ o .yourEndStep
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.harnessInfinityStone) #[] (some o.id)
  let o := namedPermanent g "The Mind Stone"
  let after := g.putMatchingSourceTriggers ⟨0⟩ o .yourEndStep
  before.waitingTriggers.isEmpty && after.waitingTriggers.size > 0

#guard infinityInactiveUntilHarnessedOk

/-!
## 424, 434 — Shield counters
-/

def shieldOk : Bool :=
  let g := mshEnter afterDraw captainAmericaSuperSoldier
  let o := namedPermanent g "Captain America, Super-Soldier"
  o.status.shield == 1 &&
    ((mshRuling 424).comment.contains "shield counter" ||
      (mshRuling 434).comment.contains "shield")

#guard shieldOk

/-!
## 19–20, 21 — Landfall (Claim the Kingdom)
-/

def landfallPlayOk : Bool :=
  let g := mshEnter afterDraw claimTheKingdom
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g forest ⟨0⟩ ⟨0⟩
  let g := settle ((g.afterLandEnters (namedPermanent g "Forest")).receivePriority ⟨0⟩) 24
  (namedPermanent g "Claim the Kingdom").status.plan == 1 &&
    (mshRuling 19).comment.contains "doesn't trigger if a permanent already" &&
    (mshRuling 20).comment.contains "triggers whenever a land you control enters"

#guard landfallPlayOk

/-- Ruling 19: a nonland entering does not trigger landfall. -/
def landfallNonlandOk : Bool :=
  let g := mshEnter afterDraw claimTheKingdom
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  (namedPermanent g "Claim the Kingdom").status.plan == 0

#guard landfallNonlandOk

/-!
## 430–433, 435 — Attacks alone
-/

def attacksAloneOk : Bool :=
  agent13SharonCarter.triggeredAbilities.any (fun ab =>
    ab == .onCreatureYouControlAttacksAloneInvestigate) &&
    ((mshRuling 430).comment.contains "attacks alone" ||
      (mshRuling 433).comment.contains "declared as an attacker")

#guard attacksAloneOk

/-!
## 534, 537 — Enrage (The Incredible Hulk)
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
    (mshRuling 537).comment.contains "enrage ability will trigger only once" &&
    (mshRuling 534).comment.contains "additional combat phase"

#guard enrageOnceOk

/-- Ruling 534: simultaneous damage (two marks before priority) is one trigger. -/
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

/-- Ruling 537: lethal damage still grants the extra combat if he was attacking. -/
def enrageLethalExtraCombatOk : Bool :=
  let g := addPermanent afterDraw theIncredibleHulk ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "The Incredible Hulk"
  let g := g.setObject { o with status := { o.status with attacking := true } }
  let o := namedPermanent g "The Incredible Hulk"
  let g := g.dealDamageToPermanent o 8
  let g := settle g 24
  !g.battlefield.any (fun x => x.name == "The Incredible Hulk") &&
    g.additionalCombatPhases == 1 &&
    (mshRuling 534).comment.contains "no longer on the battlefield"

#guard enrageLethalExtraCombatOk

/-!
## 708, 724–726 — Blazing Crescendo timing / illegal target
-/

def blazingCrescendoOk : Bool :=
  blazingCrescendo.spellEffect.isSome &&
    (mshRuling 567).comment.contains "illegal target" &&
    (mshRuling 388).comment.contains "normal timing rules" &&
    (mshRuling 724).comment.contains "You pay all costs"

#guard blazingCrescendoOk

/-- Ruling 696: Thirst for Knowledge may discard one artifact or two cards. -/
def thirstDiscardUnlessArtifactOk : Bool :=
  let g0 := addToHand afterDraw theMindStone ⟨0⟩
  let g0 := addToHand g0 lightningBolt ⟨0⟩
  let g0 := addToHand g0 mountain ⟨0⟩
  let gArt := g0.applyEffect ⟨0⟩ (Effect.drawThreeDiscardUnlessArtifact) #[]
  gArt.thirstDiscardsLeft == 2 &&
    (match gArt.pending with
     | .chooseDiscardCard ⟨0⟩ _ => true
     | _ => false) &&
    (let gArt := mustApply gArt ⟨0⟩
        (.discard (handCardNamed gArt ⟨0⟩ "The Mind Stone").id)
     gArt.thirstDiscardsLeft == 0 &&
       gArt.pending == .none &&
       (gArt.player ⟨0⟩).graveyard.any (fun id =>
         (gArt.object! id).name == "The Mind Stone")) &&
    (let gTwo := g0.applyEffect ⟨0⟩ (Effect.drawThreeDiscardUnlessArtifact) #[]
     let gTwo := mustApply gTwo ⟨0⟩
       (.discard (handCardNamed gTwo ⟨0⟩ "Lightning Bolt").id)
     gTwo.thirstDiscardsLeft == 1 &&
       (let gTwo := mustApply gTwo ⟨0⟩
          (.discard (handCardNamed gTwo ⟨0⟩ "Mountain").id)
        gTwo.thirstDiscardsLeft == 0 &&
          gTwo.pending == .none)) &&
    (mshRuling 696).comment.contains "one artifact card or two cards"

#guard thirstDiscardUnlessArtifactOk

/-!
## Shared CR principles cited by many MSH card notes
-/

def fizzleIllegalTargetOk : Bool :=
  giantGrowth.spellEffect == some (Effect.pump 3 3) &&
    uniqueMshOracleRulings.any (fun r => r.comment.contains "illegal target")

#guard fizzleIllegalTargetOk

def xIsZeroOffStackOk : Bool :=
  bruceBanner.activatedAbilities.any (fun ab =>
    ab.cost.mana.symbols.any (fun s => match s with | .x => true | _ => false)) &&
    ((mshRuling 397).comment.contains "X is 0" ||
      uniqueMshOracleRulings.any (fun r => r.comment.contains "X is 0"))

#guard xIsZeroOffStackOk

def tokenExileCeasesOk : Bool :=
  (mshRuling 159).comment.contains "token is exiled" &&
    treasureToken.isToken

#guard tokenExileCeasesOk

/-- Rulings 72–73: Hero / Villain source mana cannot pay unrestricted costs,
but can pay Hero / Villain spells and activations in any zone, including
changeling. -/
def heroSourceOk : Bool :=
  let g := addPermanent afterDraw avengersTower ⟨0⟩ ⟨0⟩
  let g := addPermanent g captainAmericaSuperSoldier ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let tower := namedPermanent g "Avengers Tower"
  let cap := namedPermanent g "Captain America, Super-Soldier"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.addAnyColorSpendOnlyHero) #[] (some tower.id)
  let pool := (g.player ⟨0⟩).manaPool
  let capPay := dummyProposal g .activatedAbility cap (ManaCost.ofColor .white)
  let bearPay := dummyProposal g .activatedAbility bears (ManaCost.ofColor .white)
  let gCh :=
    g.setObject { bears with printed := { bears.printed with keywords := Keyword.changeling } }
  let chameleon := namedPermanent gCh "Grizzly Bears"
  let gCh :=
    gCh.applyAbilityEffect ⟨0⟩ (Effect.addAnyColorSpendOnlyHero) #[] (some tower.id)
  let gGy := addToGraveyard g braveBrawler ⟨0⟩
  let gy := graveyardCardNamed gGy ⟨0⟩ "Brave Brawler"
  let gGy :=
    gGy.applyAbilityEffect ⟨0⟩ (Effect.addAnyColorSpendOnlyHero) #[] (some tower.id)
  let gHand := addToHand g braveBrawler ⟨0⟩
  let hand := handCardNamed gHand ⟨0⟩ "Brave Brawler"
  let gHand :=
    gHand.applyAbilityEffect ⟨0⟩ (Effect.addAnyColorSpendOnlyHero) #[] (some tower.id)
  let (gSp, spell) := g.allocObject captainAmericaSuperSoldier ⟨0⟩ .stack (some ⟨0⟩)
  let gSp :=
    gSp.applyAbilityEffect ⟨0⟩ (Effect.addAnyColorSpendOnlyHero) #[] (some tower.id)
  pool.heroWhite == 1 &&
    !pool.canPay (ManaCost.ofColor .white) &&
    pool.canPay (ManaCost.ofColor .white) false false true &&
    paidOk g capPay &&
    reversedPay g bearPay &&
    gCh.hasSubtype chameleon "Hero" &&
    paidOk gCh (dummyProposal gCh .activatedAbility chameleon (ManaCost.ofColor .white)) &&
    paidOk gGy (dummyProposal gGy .activatedAbility gy (ManaCost.ofColor .white)) &&
    paidOk gHand (dummyProposal gHand .activatedAbility hand (ManaCost.ofColor .white)
      (discardSource := true)) &&
    paidOk gSp (dummyProposal gSp .spell spell (ManaCost.ofColor .white)) &&
    captainAmericaSuperSoldier.hasSubtype "Hero" &&
    (mshRuling 425).comment.contains "Hero source"

#guard heroSourceOk

def villainSourceOk : Bool :=
  let g := addPermanent afterDraw villainousHideout ⟨0⟩ ⟨0⟩
  let g := addPermanent g elektraDaughterOfTheHand ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let hideout := namedPermanent g "Villainous Hideout"
  let elektra := namedPermanent g "Elektra, Daughter of the Hand"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.addAnyColorSpendOnlyVillain) #[] (some hideout.id)
  let pool := (g.player ⟨0⟩).manaPool
  let gCh :=
    g.setObject { bears with printed := { bears.printed with keywords := Keyword.changeling } }
  let chameleon := namedPermanent gCh "Grizzly Bears"
  let gCh :=
    gCh.applyAbilityEffect ⟨0⟩ (Effect.addAnyColorSpendOnlyVillain) #[] (some hideout.id)
  let gGy := addToGraveyard g elektraDaughterOfTheHand ⟨0⟩
  let gy := graveyardCardNamed gGy ⟨0⟩ "Elektra, Daughter of the Hand"
  let gGy :=
    gGy.applyAbilityEffect ⟨0⟩ (Effect.addAnyColorSpendOnlyVillain) #[] (some hideout.id)
  pool.villainBlack == 1 &&
    !pool.canPay (ManaCost.ofColor .black) &&
    pool.canPay (ManaCost.ofColor .black) false false false true &&
    paidOk g (dummyProposal g .activatedAbility elektra (ManaCost.ofColor .black)) &&
    reversedPay g (dummyProposal g .activatedAbility bears (ManaCost.ofColor .black)) &&
    gCh.hasSubtype chameleon "Villain" &&
    paidOk gCh (dummyProposal gCh .activatedAbility chameleon (ManaCost.ofColor .black)) &&
    paidOk gGy (dummyProposal gGy .activatedAbility gy (ManaCost.ofColor .black)) &&
    elektraDaughterOfTheHand.hasSubtype "Villain" &&
    (mshRuling 426).comment.contains "Villain source"

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
    (mshRuling 383).comment.contains "exiled instead" &&
    (mshRuling 385).comment.contains "any permanent" &&
    (mshRuling 387).comment.contains "redundant"

#guard finalityExileOk

def finalityOtherZoneOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Grizzly Bears"
  let g := g.addFinalityTo o 1
  let o := namedPermanent g "Grizzly Bears"
  let g := g.returnToHand o.id ⟨0⟩
  (g.player ⟨0⟩).hand.any (fun id => (g.object! id).name == "Grizzly Bears") &&
    (mshRuling 384).comment.contains "owner's hand"

#guard finalityOtherZoneOk

def winterSoldierFinalityOk : Bool :=
  let g := addToGraveyard afterDraw winterSoldierIcyAssassin ⟨0⟩
  let o :=
    match g.objects.find? (fun x =>
      x.name == "Winter Soldier, Icy Assassin" && x.zone == .graveyard ⟨0⟩) with
    | some x => x
    | none => namedPermanent afterDraw "Grizzly Bears"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.returnFromGyFinalityAttach) #[] (some o.id)
  (namedPermanent g "Winter Soldier, Icy Assassin").status.finality ≥ 1

#guard winterSoldierFinalityOk

def daredevilLookOk : Bool :=
  daredevilManWithoutFear.mayLookAtTopAnytime &&
    (mshRuling 466).comment.contains "look at the top card"

#guard daredevilLookOk

/-- Ruling 443: Ant-Man's second ability triggers on any +1/+1 counter. -/
def antManAnyCounterOk : Bool :=
  let g := addPermanent afterDraw antManColonyCommander ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.addPlusOnePlusOneTo bears 1
  let insect :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.youPutPlusOne)).size
  insect == 1 &&
    (namedPermanent g "Grizzly Bears").status.plusOnePlusOne == 1 &&
    (let ant := namedPermanent g "Ant-Man, Colony Commander"
     ant.status.firedOnceEachTurn &&
       (let g := g.addPlusOnePlusOneTo (namedPermanent g "Grizzly Bears") 1
        (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
          t.event == TriggerEvent.youPutPlusOne)).size == 1)) &&
    (mshRuling 443).comment.contains "for any reason"

#guard antManAnyCounterOk

/-!
## 393, 407–409, 609, 683 — Improvise
-/

def improviseReduceOk : Bool :=
  let cost : ManaCost := { symbols := #[.generic 3, .colored .blue] }
  let reduced := Game.improviseReduce cost 2
  reduced == ({ symbols := #[.generic 1, .colored .blue] } : ManaCost) &&
    (Game.improviseReduce cost 3) == ({ symbols := #[.colored .blue] } : ManaCost) &&
    arcReactor.hasImprovise &&
    ironheartCleverChampion.grantsImproviseToNoncreature &&
    (mshRuling 407).comment.contains "cost of casting the spell" &&
    (mshRuling 408).comment.contains "Improvise can't pay" &&
    (mshRuling 409).comment.contains "doesn't change a spell's mana cost" &&
    (mshRuling 609).comment.contains "Multiple instances of improvise" &&
    (mshRuling 683).comment.contains "first choose the value for X" &&
    (mshRuling 393).comment.contains "isn't an alternative cost"

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

/-- Ruling 399: a tapped artifact cannot be tapped again for improvise. -/
def improviseAlreadyTappedOk : Bool :=
  let (g, tok) := afterDraw.createToken ⟨0⟩ treasureToken
  let g := g.setObject { tok with status := { tok.status with tapped := true } }
  match g.tapArtifactsForImprovise ⟨0⟩ #[tok.id] with
  | .error msg =>
    msg.contains "already tapped" &&
      (mshRuling 399).comment.contains "won't be able to tap it again"
  | .ok _ => false

#guard improviseAlreadyTappedOk

/-!
## 429, 511, 526, 533 — Boast
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
    (mshRuling 429).comment.contains "declared as an attacker" &&
    (mshRuling 511).comment.contains "never declared as an attacker" &&
    (mshRuling 526).comment.contains "only once" &&
    (mshRuling 533).comment.contains "hasn't been activated yet that turn"

#guard boastWindowOk

/-- Ruling 511: entering attacking does not unlock boast. -/
def boastEnteredAttackingOk : Bool :=
  let g := addPermanent afterDraw baronHelmutZemo ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Baron Helmut Zemo"
  let g := g.setObject { o with status := { o.status with attacking := true } }
  !g.canActivateBoast (namedPermanent g "Baron Helmut Zemo")

#guard boastEnteredAttackingOk

/-!
## 510, 636 — Sneak
-/

def sneakCostOk : Bool :=
  elektraDaughterOfTheHand.sneakCost ==
      some ({ symbols := #[.generic 1, .colored .black, .colored .black] } : ManaCost) &&
    !afterDraw.canCastForSneak ⟨0⟩ &&
    (let g := { afterDraw with step := .declareBlockers, activePlayer := ⟨0⟩ }
     g.canCastForSneak ⟨0⟩ && !g.canCastForSneak ⟨1⟩) &&
    (let g := { afterDraw with step := .declareAttackers, activePlayer := ⟨0⟩ }
     !g.canCastForSneak ⟨0⟩) &&
    (mshRuling 510).comment.contains "enters tapped and attacking" &&
    (mshRuling 636).comment.contains "declare blockers step"

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
## 471–472 — Equip worthy
-/

def equipWorthyOk : Bool :=
  mjLnirHammerOfThor.hasEquipWorthy &&
    mjLnirHammerOfThor.activatedAbilities[0]!.equipWorthy &&
    captainAmericaSuperSoldier.isWorthy &&
    !elektraDaughterOfTheHand.isWorthy &&
    !lokiGodOfMischief.isWorthy &&
    !grizzlyBears.isWorthy &&
    (let ab := mjLnirHammerOfThor.activatedAbilities[0]!
     let gCap := addPermanent afterDraw mjLnirHammerOfThor ⟨0⟩ ⟨0⟩
     let gCap := addPermanent gCap captainAmericaSuperSoldier ⟨0⟩ ⟨0⟩
     let gCap := withRedMana gCap ⟨0⟩ 1
     let gLoki := addPermanent afterDraw mjLnirHammerOfThor ⟨0⟩ ⟨0⟩
     let gLoki := addPermanent gLoki lokiGodOfMischief ⟨0⟩ ⟨0⟩
     let gLoki := withRedMana gLoki ⟨0⟩ 1
     gCap.canActivate ⟨0⟩ (namedPermanent gCap "Mjölnir, Hammer of Thor") ab &&
       !gLoki.canActivate ⟨0⟩ (namedPermanent gLoki "Mjölnir, Hammer of Thor") ab &&
       (let g := addPermanent afterDraw mjLnirHammerOfThor ⟨0⟩ ⟨0⟩
        let g := addPermanent g captainAmericaSuperSoldier ⟨0⟩ ⟨0⟩
        let g := addPermanent g lokiGodOfMischief ⟨0⟩ ⟨0⟩
        let g := withRedMana g ⟨0⟩ 1
        let hammer := namedPermanent g "Mjölnir, Hammer of Thor"
        let cap := namedPermanent g "Captain America, Super-Soldier"
        let loki := namedPermanent g "Loki, God of Mischief"
        let gEq := mustApply g ⟨0⟩ (.activate hammer.id 0)
        match gEq.pending, gEq.objectAwaitingTargets with
        | .chooseTargets ⟨0⟩, some awaiting =>
          let legal := gEq.legalProposedTargets ⟨0⟩ awaiting
          legal.contains (Target.permanent cap.id) &&
            !legal.contains (Target.permanent loki.id) &&
            (match gEq.apply ⟨0⟩ (.target (Target.permanent loki.id)) with
             | .error msg => mentions msg "Illegal target"
             | .ok _ => false)
        | _, _ => false) &&
       (let g := addPermanent afterDraw mjLnirHammerOfThor ⟨0⟩ ⟨0⟩
        let g := addPermanent g lokiGodOfMischief ⟨0⟩ ⟨0⟩
        let g := addPermanent g superSoldierSerum ⟨0⟩ ⟨0⟩
        let hammer := namedPermanent g "Mjölnir, Hammer of Thor"
        let loki := namedPermanent g "Loki, God of Mischief"
        let serum := namedPermanent g "Super-Soldier Serum"
        let g := g.attachSourceTo serum loki
        let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchEnchantedAttachEquipment)
          (some (namedPermanent g "Super-Soldier Serum").id)
          #[Target.permanent hammer.id]
        (namedPermanent g "Mjölnir, Hammer of Thor").attachedTo == some loki.id)) &&
    (mshRuling 471).comment.contains "isn't worthy" &&
    (mshRuling 472).comment.contains "Equip worthy"

#guard equipWorthyOk

/-!
## 672, 699 — Vibranium tokens
-/

def vibraniumTokenOk : Bool :=
  let g := afterDraw.createKindTokens ⟨0⟩ .vibranium 1
  let o := namedPermanent g "Vibranium"
  o.printed.isToken && o.printed.hasSubtype "Vibranium" &&
    o.printed.keywords.indestructible &&
    g.hasIndestructible o &&
    (mshRuling 672).comment.contains "predefined token" &&
    (mshRuling 699).comment.contains "isn't a nonartifact spell"

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

/-- Ruling 515 / 274 / 281: one shield counter prevents one damage or destroy. -/
def shieldPreventsDestroyOk : Bool :=
  let g := mshEnter afterDraw captainAmericaSuperSoldier
  let o := namedPermanent g "Captain America, Super-Soldier"
  let g := g.destroyPermanent o
  g.battlefield.any (fun x => x.name == "Captain America, Super-Soldier") &&
    (namedPermanent g "Captain America, Super-Soldier").status.shield == 0 &&
    (mshRuling 626).comment.contains "isn't the same as regenerating" &&
    (mshRuling 633).comment.contains "sacrificing"

#guard shieldPreventsDestroyOk

/-- Ruling 397 / 161: {X} is 0 off the stack. -/
def xOffStackIsZeroOk : Bool :=
  photonBlastBarrage.manaCost.symbols.any (fun
    | .x => true
    | _ => false) &&
    photonBlastBarrage.manaValue == 2 &&
    ((mshRuling 397).comment.contains "X is 0" ||
      (mshRuling 513).comment.contains "X is 0")

#guard xOffStackIsZeroOk

/-- Ruling 159 / 158: an exiled token ceases to exist. -/
def tokenExileCeasesToExistOk : Bool :=
  let (g, tok) := afterDraw.createToken ⟨0⟩ treasureToken
  let (g, _) := g.move tok.id .exile none
  let g := g.checkSBA
  !g.objects.any (fun o => o.name == "Treasure") &&
    g.log.any (fun s => mentions s "ceases to exist") &&
    (mshRuling 159).comment.contains "cease to exist" &&
    (mshRuling 149).comment.contains "ceases to exist"

#guard tokenExileCeasesToExistOk

/-!
## 456, 480, 689, 693–694 — Power-up interactions
-/

/-- Ruling 456: Bold Biochemist's power-up still draws if it has left. -/
def boldBiochemistDrawsAfterLeaveOk : Bool :=
  let g := addPermanent afterDraw boldBiochemist ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Bold Biochemist"
  let hand0 := (g.player ⟨0⟩).hand.size
  let (g, _) := g.move o.id (.graveyard ⟨0⟩) none
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.plusOneAndDraw 1 2) #[] (some o.id)
  (g.player ⟨0⟩).hand.size == hand0 + 2 &&
    !g.battlefield.any (fun x => x.name == "Bold Biochemist") &&
    (mshRuling 456).comment.contains "you'll still draw two cards"

#guard boldBiochemistDrawsAfterLeaveOk

/-- Ruling 480: Hulk reduces only generic mana on other creatures' power-up. -/
def hulkPowerUpGenericOnlyOk : Bool :=
  let g := addPermanent afterDraw hulkGammaGoliath ⟨0⟩ ⟨0⟩
  let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
  let bot := namedPermanent g "Aerial Doombot"
  let ab := bot.printed.activatedAbilities[0]!
  let cost := g.activationManaCost ⟨0⟩ ab (some bot)
  cost.coloredCount .blue == 1 &&
    cost.manaValue == ab.cost.mana.manaValue - 3 &&
    (mshRuling 480).comment.contains "only the amount of generic mana"

#guard hulkPowerUpGenericOnlyOk

/-- Ruling 689 / 342: Wonder Man lets each power-up be activated twice,
including his own. -/
def wonderManExtraPowerUpOk : Bool :=
  let g := addPermanent afterDraw wonderManHollywoodHero ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Wonder Man, Hollywood Hero"
  let ab := o.printed.activatedAbilities[0]!
  g.powerUpActivationLimit ⟨0⟩ == 2 &&
    g.canActivate ⟨0⟩ o ab &&
    (let g := g.mapObjectStatus o (fun s => { s with powerUpUsed := true, powerUpActivations := 1 })
     let o := namedPermanent g "Wonder Man, Hollywood Hero"
     g.canActivate ⟨0⟩ o ab &&
       (let g := g.mapObjectStatus o (fun s => { s with powerUpActivations := 2 })
        !g.canActivate ⟨0⟩ (namedPermanent g "Wonder Man, Hollywood Hero") ab)) &&
    (mshRuling 689).comment.contains "twice rather than once" &&
    (mshRuling 694).comment.contains "own power-up ability"

#guard wonderManExtraPowerUpOk

/-- Ruling 693: each Wonder Man adds one extra activation. -/
def twoWonderMenThreeActivationsOk : Bool :=
  let g := addPermanent afterDraw wonderManHollywoodHero ⟨0⟩ ⟨0⟩
  let g := addPermanent g wonderManHollywoodHero ⟨0⟩ ⟨0⟩
  let n :=
    (g.permanentsOf ⟨0⟩).filter Game.grantsExtraPowerUp |>.size
  n == 2 &&
    g.powerUpActivationLimit ⟨0⟩ == 3 &&
    (mshRuling 693).comment.contains "two of him"

#guard twoWonderMenThreeActivationsOk

/-!
## 380, 390, 396, 398, 404, 413, 416–418, 420, 427–428, 436, 440, 444,
## 481, 505–507, 514, 520, 528, 665 — Shared CR on MSH cards
-/

def mdfcPlayFaceOk : Bool :=
  let g := addToHand afterDraw bruceBanner ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Bruce Banner"
  g.canCast ⟨0⟩ card &&
    g.objectManaValue card == 1 &&
    bruceBanner.manaValue <= 2 &&
    theIncredibleHulk.manaValue > 2 &&
    (mshRuling 380).comment.contains "face you're playing"

#guard mdfcPlayFaceOk

def activatedVsTriggeredWordingOk : Bool :=
  aerialDoombot.activatedAbilities.any (·.powerUp) &&
    claimTheKingdom.triggeredAbilities.size > 0 &&
    (mshRuling 390).comment.contains "colon" &&
    (mshRuling 417).comment.contains "when"

#guard activatedVsTriggeredWordingOk

def equipmentTapIndependentOk : Bool :=
  let g := addPermanent afterDraw captainAmericaSuperSoldier ⟨0⟩ ⟨0⟩
  let g := addPermanent g captainAmericaSShield ⟨0⟩ ⟨0⟩
  let cap := namedPermanent g "Captain America, Super-Soldier"
  let sh := namedPermanent g "Captain America's Shield"
  let g := g.attachSourceTo sh cap
  let cap := namedPermanent g "Captain America, Super-Soldier"
  let g := g.mapObjectStatus cap (fun s => { s with tapped := true })
  let sh := namedPermanent g "Captain America's Shield"
  !sh.status.tapped &&
    (mshRuling 396).comment.contains "doesn't become tapped"

#guard equipmentTapIndependentOk

def xZeroWithoutPayingOk : Bool :=
  let g := addToHand afterDraw photonBlastBarrage ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Photon Blast Barrage"
  let card := { card with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }
  g.playManaCost card photonBlastBarrage == ManaCost.zero &&
    (mshRuling 398).comment.contains "choose 0"

#guard xZeroWithoutPayingOk

def copyKeepsXAndIsNotCastOk : Bool :=
  let (g, src) := afterDraw.allocObject photonBlastBarrage ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.setObject { src with chosenX := some 3 }
  let g := g.copyStackSpell (g.object! src.id) ⟨0⟩
  let copies := g.objects.filter (fun o =>
    o.name == "Photon Blast Barrage" && o.zone == .stack && o.isCopy)
  copies.size == 1 && copies[0]!.chosenX == some 3 &&
    copies[0]!.isCopy &&
    (mshRuling 404).comment.contains "same value of X" &&
    (mshRuling 413).comment.contains "not \"cast.\"" &&
    (mshRuling 420).comment.contains "additional costs for the copy"

#guard copyKeepsXAndIsNotCastOk

def totalCostIncludesAdditionalOk : Bool :=
  helicarrierStrike.teamwork == some 2 &&
    helicarrierStrike.manaCost.manaValue == 1 &&
    (mshRuling 416).comment.contains "total cost of a spell" &&
    (mshRuling 418).comment.contains "additional costs" &&
    (mshRuling 665).comment.contains "total cost of a spell"

#guard totalCostIncludesAdditionalOk

def creatureAndArtifactSourceOk : Bool :=
  let g := addPermanent afterDraw echoPerceptiveProdigy ⟨0⟩ ⟨0⟩
  let g := addPermanent g shangChiMasterOfKungFu ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g theMindStone ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let stone := namedPermanent g "The Mind Stone"
  let shang := namedPermanent g "Shang-Chi, Master of Kung Fu"
  let (g, bearAb) := g.putStackAbility bears ⟨0⟩
    (abilityEffect := some (Effect.abilityDraw 1))
  let (g, stoneAb) := g.putStackAbility stone ⟨0⟩
    (abilityEffect := some (Effect.abilityDraw 1))
  let creatureLegal :=
    g.legalTargetsForKind ⟨0⟩ .stackAbilityFromCreatureSource
  let artifactLegal :=
    g.legalTargetsForKind ⟨0⟩ .stackAbilityFromArtifactSource
  let gMana :=
    g.applyAbilityEffect ⟨0⟩ (Effect.addTwoAnyColorCreatureSources) #[] (some shang.id)
  let pool := (gMana.player ⟨0⟩).manaPool
  creatureLegal.contains (Target.card bearAb.id) &&
    !creatureLegal.contains (Target.card stoneAb.id) &&
    artifactLegal.contains (Target.card stoneAb.id) &&
    !artifactLegal.contains (Target.card bearAb.id) &&
    echoPerceptiveProdigy.activatedAbilities[0]!.effect.targetKind ==
      .stackAbilityFromCreatureSource &&
    pool.creatureGreen == 2 &&
    !pool.canPay (ManaCost.ofGeneric 2) &&
    pool.canPay (ManaCost.ofGeneric 2) false false false false false true &&
    paidOk gMana (dummyProposal gMana .activatedAbility bears (ManaCost.ofGeneric 2)) &&
    reversedPay gMana (dummyProposal gMana .activatedAbility stone (ManaCost.ofGeneric 2)) &&
    (let gGy := addToGraveyard gMana grizzlyBears ⟨0⟩
     let gy := graveyardCardNamed gGy ⟨0⟩ "Grizzly Bears"
     paidOk gGy (dummyProposal gGy .activatedAbility gy (ManaCost.ofGeneric 2))) &&
    (let (gSp, spell) := gMana.allocObject grizzlyBears ⟨0⟩ .stack (some ⟨0⟩)
     reversedPay gSp (dummyProposal gSp .spell spell (ManaCost.ofGeneric 2))) &&
    (mshRuling 427).comment.contains "creature source" &&
    (mshRuling 428).comment.contains "creature" &&
    (mshRuling 440).comment.contains "artifact source"

#guard creatureAndArtifactSourceOk

def poisonTenLosesOk : Bool :=
  let g := afterDraw.modifyPlayer ⟨0⟩ (fun pl => { pl with poison := 10 })
  let g := g.checkSBA
  (g.player ⟨0⟩).lost &&
    g.log.any (fun s => mentions s "poison") &&
    (mshRuling 436).comment.contains "ten or more poison"

#guard poisonTenLosesOk

def copiesYouDontCastCeaseOk : Bool :=
  let (g, src) := afterDraw.allocObject helicarrierStrike ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.copyStackSpell src ⟨0⟩
  let copy := (g.objects.filter (fun o => o.isCopy))[0]!
  let (g, _) := g.move copy.id .exile none
  let g := g.checkSBA
  !g.objects.any (fun o => o.isCopy) &&
    (mshRuling 444).comment.contains "cease to exist"

#guard copiesYouDontCastCeaseOk

def hybridBlackCountsOk : Bool :=
  bullseyeDeathDealer.manaCost.symbolsIncludingColor .black == 1 &&
    ghostSpectralSaboteur.manaCost.symbolsIncludingColor .black == 1 &&
    baronHelmutZemo.manaCost.symbolsIncludingColor .black == 3 &&
    lightningBolt.manaCost.symbolsIncludingColor .black == 0 &&
    (let g15 :=
      (List.range 15).foldl (fun g _ => addToGraveyard g bullseyeDeathDealer ⟨0⟩)
        afterDraw
     let ids15 :=
       g15.objects.filter (fun o =>
         o.name == "Bullseye, Death Dealer" && o.zone == .graveyard ⟨0⟩) |>.map (·.id)
     g15.canPayZemoBoast ⟨0⟩ ids15 &&
       g15.zemoBoastBlackSymbols ids15 == 15) &&
    (let g14 :=
      (List.range 14).foldl (fun g _ => addToGraveyard g bullseyeDeathDealer ⟨0⟩)
        afterDraw
     let ids14 :=
       g14.objects.filter (fun o =>
         o.name == "Bullseye, Death Dealer" && o.zone == .graveyard ⟨0⟩) |>.map (·.id)
     !g14.canPayZemoBoast ⟨0⟩ ids14 &&
       g14.zemoBoastBlackSymbols ids14 == 14) &&
    (let gMix := addToGraveyard afterDraw lightningBolt ⟨0⟩
     let gMix :=
       (List.range 14).foldl (fun g _ => addToGraveyard g bullseyeDeathDealer ⟨0⟩)
         gMix
     let idsMix :=
       gMix.objects.filter (fun o =>
         o.zone == .graveyard ⟨0⟩) |>.map (·.id)
     !gMix.canPayZemoBoast ⟨0⟩ idsMix) &&
    (mshRuling 481).comment.contains "Hybrid mana symbols that include black"

#guard hybridBlackCountsOk

def xIsZeroInZonesOk : Bool :=
  let g := addToHand afterDraw photonBlastBarrage ⟨0⟩
  let g := addToGraveyard g photonBlastBarrage ⟨0⟩
  let g := addToLibraryTop g photonBlastBarrage ⟨0⟩
  let g := addPermanent g photonBlastBarrage ⟨0⟩ ⟨0⟩
  let hand := handCardNamed g ⟨0⟩ "Photon Blast Barrage"
  let gy :=
    match g.objects.find? (fun o =>
      o.name == "Photon Blast Barrage" && o.zone == .graveyard ⟨0⟩) with
    | some o => o
    | none => hand
  let lib :=
    match g.objects.find? (fun o =>
      o.name == "Photon Blast Barrage" && match o.zone with | .library _ => true | _ => false) with
    | some o => o
    | none => hand
  let bf := namedPermanent g "Photon Blast Barrage"
  g.objectManaValue hand == 2 &&
    g.objectManaValue gy == 2 &&
    g.objectManaValue lib == 2 &&
    g.objectManaValue bf == 2 &&
    (mshRuling 397).comment.contains "X is 0" &&
    (mshRuling 505).comment.contains "X is 0" &&
    (mshRuling 506).comment.contains "X is 0" &&
    (mshRuling 507).comment.contains "X is 0" &&
    (mshRuling 513).comment.contains "X is 0" &&
    (mshRuling 514).comment.contains "X is 0" &&
    (mshRuling 520).comment.contains "value chosen for X"

#guard xIsZeroInZonesOk

/-- Ruling 528: tapping an already-tapped creature is not becoming tapped. -/
def tapAlreadyTappedOk : Bool :=
  let g := addPermanent afterDraw captainAmericaLivingLegend ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Captain America, Living Legend"
  let g := g.setObject { o with status := { o.status with tapped := true } }
  let o := g.object! o.id
  let g := g.applyPermanentAction o PermanentAction.tap
  let o2 := g.object! o.id
  o.status.tapped && o2.status.tapped &&
    logContains g "already tapped" &&
    !logContains g "becomes tapped" &&
    (mshRuling 528).comment.contains "already tapped"

#guard tapAlreadyTappedOk

/-!
## 392–89, 411, 453–454 — Exile leaves Auras and Equipment behind
-/

def exileUnattachesOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g superSoldierSerum ⟨0⟩ ⟨0⟩
  let g := addPermanent g captainAmericaSShield ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let aura := namedPermanent g "Super-Soldier Serum"
  let eq := namedPermanent g "Captain America's Shield"
  let g := g.attachSourceTo aura host
  let g := g.attachSourceTo eq host
  let (g, _) := g.move (namedPermanent g "Grizzly Bears").id .exile none
  let g := g.checkSBA
  let aura := namedGraveyardCard g ⟨0⟩ "Super-Soldier Serum"
  let eq := namedPermanent g "Captain America's Shield"
  aura.zone == .graveyard ⟨0⟩ &&
    eq.isOnBattlefield && eq.attachedTo.isNone &&
    (mshRuling 392).comment.contains "Equipment will become unattached" &&
    (mshRuling 89).comment.contains "remain on the battlefield" &&
    (mshRuling 453).comment.contains "Auras attached" &&
    (mshRuling 454).comment.contains "Equipment attached"

#guard exileUnattachesOk

def returnedIsNewObjectOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let old := namedPermanent g "Grizzly Bears"
  let oldId := old.id
  let g := g.setObject { old with status :=
    { old.status with plusOnePlusOne := 2, attacking := true } }
  let (g, _) := g.move oldId .exile none
  let gy :=
    match g.objects.find? (fun o => o.name == "Grizzly Bears") with
    | some o => o
    | none => old
  let (g, newId) := g.putOntoBattlefield gy.id ⟨0⟩
  let back := g.object! newId
  back.id != oldId &&
    back.status.plusOnePlusOne == 0 &&
    !back.status.attacking &&
    (mshRuling 411).comment.contains "new object"

#guard returnedIsNewObjectOk

/-!
## 21, 422, 431–432, 435, 438–439, 464 — Landfall / once each turn / attacks
-/

def landfallEachAbilityOk : Bool :=
  let g := mshEnter afterDraw claimTheKingdom
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g forest ⟨0⟩ ⟨0⟩
  let g := settle ((g.afterLandEnters (namedPermanent g "Forest")).receivePriority ⟨0⟩) 24
  (namedPermanent g "Claim the Kingdom").status.plan == 1 &&
    (mshRuling 21).comment.contains "each landfall ability"

#guard landfallEachAbilityOk

/-- Ruling 422: declining the optional connive does not lock the ability;
choosing it does, and already-stacked instances then do nothing. -/
def onceEachTurnConniveWordingOk : Bool :=
  let villainWait (g : Game) : Nat :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.anotherVillainEnters)).size
  let g0 := addPermanent afterDraw baronStruckerHYDRAOverlord ⟨0⟩ ⟨0⟩
  let struckerId := (namedPermanent g0 "Baron Strucker, HYDRA Overlord").id
  let g := addPermanent g0 redGuardianSuperSoldier ⟨0⟩ ⟨0⟩
  let rg := namedPermanent g "Red Guardian, Super-Soldier"
  let g := g.afterPermanentEnters rg
  let w1 := villainWait g
  let strucker := namedPermanent g "Baron Strucker, HYDRA Overlord"
  w1 == 1 &&
    !strucker.status.firedOnceEachTurn &&
    !strucker.status.optionalOnceUsed &&
    (let gAsk := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchVillainConniveOnce)
       (some struckerId)
     match gAsk.pending with
     | .mayHaveVillainConnive ⟨0⟩ src vid =>
       src == struckerId && vid == rg.id &&
         (let gDec := mustApply gAsk ⟨0⟩ .decline
          let strucker := namedPermanent gDec "Baron Strucker, HYDRA Overlord"
          !strucker.status.optionalOnceUsed &&
            (gDec.player ⟨0⟩).hand.size == (g.player ⟨0⟩).hand.size &&
            (let g2 := addPermanent gDec baronHelmutZemo ⟨0⟩ ⟨0⟩
             let g2 := g2.afterPermanentEnters (namedPermanent g2 "Baron Helmut Zemo")
             villainWait g2 == w1 + 1))
     | _ => false) &&
    (let hand0 := (g.player ⟨0⟩).hand.size
     let gAsk := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchVillainConniveOnce)
       (some struckerId) #[Target.permanent rg.id]
     match gAsk.pending with
     | .mayHaveVillainConnive ⟨0⟩ _ _ =>
       let gYes := mustApply gAsk ⟨0⟩ .haveVillainConnive
       let strucker := namedPermanent gYes "Baron Strucker, HYDRA Overlord"
       strucker.status.optionalOnceUsed &&
         (gYes.player ⟨0⟩).hand.size == hand0 + 1 &&
         (let wYes := villainWait gYes
          let g3 := addPermanent gYes baronHelmutZemo ⟨0⟩ ⟨0⟩
          let g3 := g3.afterPermanentEnters (namedPermanent g3 "Baron Helmut Zemo")
          villainWait g3 == wYes) &&
         (let gNo := gYes.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchVillainConniveOnce)
            (some struckerId) #[Target.permanent rg.id]
          (gNo.player ⟨0⟩).hand.size == (gYes.player ⟨0⟩).hand.size &&
            gNo.log.any (fun s => mentions s "no effect"))
     | _ => false) &&
    (mshRuling 422).comment.contains "Do this only once each turn"

#guard onceEachTurnConniveWordingOk

def enterAttackingNotDeclaredOk : Bool :=
  let g := addPermanent afterDraw baronHelmutZemo ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Baron Helmut Zemo"
  let g := g.setObject { o with status := { o.status with attacking := true } }
  !g.canActivateBoast (namedPermanent g "Baron Helmut Zemo") &&
    (mshRuling 438).comment.contains "never declared as an attacking creature" &&
    (mshRuling 439).comment.contains "never declared" &&
    (mshRuling 464).comment.contains "enter attacking"

#guard enterAttackingNotDeclaredOk

def attacksAloneWordingOk : Bool :=
  (mshRuling 431).comment.contains "attacks alone" &&
    (mshRuling 432).comment.contains "declare attackers step" &&
    (mshRuling 435).comment.contains "currently attacking"

#guard attacksAloneWordingOk

/-!
## 561–571 — Illegal targets cause the spell or ability to do nothing
-/

/-- Rulings 209–219: an illegal creature target fizzles the whole spell or
ability, including untargeted extras (life, draw, surveil, exile, damage). -/
def illegalTargetDoesNothingOk : Bool :=
  let g0 := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g0 "Grizzly Bears"
  let (gGone, _) := g0.move bears.id (.graveyard ⟨0⟩) none
  let gone := #[Target.permanent bears.id]
  let hand0 := (gGone.player ⟨0⟩).hand.size
  let life0 := (gGone.player ⟨0⟩).life
  let lib0 := (gGone.player ⟨0⟩).library.size
  let plan0 :=
    let g := addPermanent gGone claimTheKingdom ⟨0⟩ ⟨0⟩
    (namedPermanent g "Claim the Kingdom").status.plan
  let gDepower := gGone.applyEffect ⟨0⟩ (Effect.pumpThenDraw (-4) 0) gone
  let gHour := gGone.applyEffect ⟨0⟩ (Effect.destroyCreatureSurveil) gone
  let gPym := gGone.applyEffect ⟨0⟩ (Effect.grantVigilanceUnblockable) gone
  let gCrescendo :=
    gGone.applyEffect ⟨0⟩ (Effect.pumpThenExileTopPlay 3 1) gone
  let gRepulsor :=
    gGone.applyEffect ⟨0⟩ (Effect.dealDamageThenControllerIfTeamwork 5 2) gone
  let gCruel :=
    gGone.applyEffect ⟨0⟩ (Effect.exileCreatureMvAtMostOrAnyIfTeamwork 3 3) gone
  let gCrowd :=
    gGone.applyAbilityEffect ⟨0⟩ (Effect.pumpAttackingAloneGainLife) gone
  let gLandfall :=
    let g := addPermanent gGone claimTheKingdom ⟨0⟩ ⟨0⟩
    let plan := namedPermanent g "Claim the Kingdom"
    g.applyTriggeredAbility ⟨0⟩ (.onLandYouControlEntersPlusOneAndPlan) (some plan.id)
      gone
  let gAbsorb :=
    let g := addPermanent gGone absorbingMan ⟨0⟩ ⟨0⟩
    g.applyModeledTrigger ⟨0⟩ (.onStep Effect.stepCopyAbsorbingMan)
      (some (namedPermanent g "Absorbing Man").id) gone
  let gTask :=
    let g := addPermanent gGone taskmasterMercenaryMimic ⟨0⟩ ⟨0⟩
    g.applyModeledTrigger ⟨0⟩ (.onStep Effect.stepCopyTaskmaster)
      (some (namedPermanent g "Taskmaster, Mercenary Mimic").id) gone
  (gDepower.player ⟨0⟩).hand.size == hand0 &&
    (gHour.player ⟨0⟩).library.size == lib0 &&
    (gPym.player ⟨0⟩).hand.size == hand0 &&
    (gCrescendo.player ⟨0⟩).library.size == lib0 &&
    (gRepulsor.player ⟨1⟩).life == (gGone.player ⟨1⟩).life &&
    (gCruel.player ⟨0⟩).life == life0 &&
    (gCrowd.player ⟨0⟩).life == life0 &&
    (namedPermanent gLandfall "Claim the Kingdom").status.plan == plan0 &&
    !(namedPermanent gAbsorb "Absorbing Man").printed.subtypes.any (· == "Bear") &&
    !(namedPermanent gTask "Taskmaster, Mercenary Mimic").printed.subtypes.any
      (· == "Bear") &&
    (mshRuling 561).comment.contains "won't gain life" &&
    (mshRuling 562).comment.contains "Cruel Alliance" &&
    (mshRuling 563).comment.contains "Depower" &&
    (mshRuling 564).comment.contains "Hour of Defeat" &&
    (mshRuling 565).comment.contains "Pym Particles" &&
    (mshRuling 566).comment.contains "Repulsor Blast" &&
    (mshRuling 567).comment.contains "illegal target" &&
    (mshRuling 568).comment.contains "will not resolve" &&
    (mshRuling 569).comment.contains "Taskmaster" &&
    (mshRuling 570).comment.contains "landfall ability" &&
    (mshRuling 571).comment.contains "Absorbing Man"

#guard illegalTargetDoesNothingOk

/-- Giant Growth does nothing if its target has left (shared CR / ruling 180). -/
def fizzleWhenTargetLeftOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let host := namedPermanent g "Grizzly Bears"
  let (g, _) := g.move host.id (.graveyard ⟨1⟩) none
  g.legalTargets ⟨0⟩ (Effect.pump 3 3) |>.isEmpty &&
    (mshRuling 532).comment.contains "illegal target"

#guard fizzleWhenTargetLeftOk

/-!
## 386, 466, 592, 595 — Look at the top card
-/

def lookAtTopRestrictionOk : Bool :=
  let g := addPermanent afterDraw daredevilManWithoutFear ⟨0⟩ ⟨0⟩
  let g := addPermanent g ironLadDivergingDestiny ⟨0⟩ ⟨0⟩
  let g := addPermanent g kaZarOfTheSavageLand ⟨0⟩ ⟨0⟩
  g.canLookAtLibraryTop ⟨0⟩ &&
    !({ g with castingFromTop := true }).canLookAtLibraryTop ⟨0⟩ &&
    daredevilManWithoutFear.mayLookAtTopAnytime &&
    ironLadDivergingDestiny.mayLookAtTopAnytime &&
    kaZarOfTheSavageLand.mayLookAtTopAnytime &&
    (mshRuling 386).comment.contains "can't look at the n" &&
    (mshRuling 466).comment.contains "look at the top card" &&
    (mshRuling 592).comment.contains "look at the top card" &&
    (mshRuling 595).comment.contains "look at the top card"

#guard lookAtTopRestrictionOk

/-!
## 672 already covered; 697–699 Vibranium spend
-/

def vibraniumSpendNotOnNonartifactOk : Bool :=
  let g := afterDraw.createKindTokens ⟨0⟩ .vibranium 1
  let vib := namedPermanent g "Vibranium"
  match g.tapForMana ⟨0⟩ vib.id .colorless with
  | .error _ => false
  | .ok g =>
    let p := (g.player ⟨0⟩).manaPool
    let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
    let g := addPermanent g theMindStone ⟨0⟩ ⟨0⟩
    let bears := namedPermanent g "Grizzly Bears"
    let stone := namedPermanent g "The Mind Stone"
    let (gArt, artSpell) := g.allocObject theMindStone ⟨0⟩ .stack (some ⟨0⟩)
    let (gBolt, bolt) := g.allocObject lightningBolt ⟨0⟩ .stack (some ⟨0⟩)
    p.cantNonartifact == 1 &&
      !p.canPay (ManaCost.ofGeneric 1) &&
      p.canPay (ManaCost.ofGeneric 1) false false false false true &&
      paidOk g (dummyProposal g .activatedAbility bears (ManaCost.ofGeneric 1)) &&
      paidOk g (dummyProposal g .activatedAbility stone (ManaCost.ofGeneric 1)) &&
      paidOk gArt (dummyProposal gArt .spell artSpell (ManaCost.ofGeneric 1)) &&
      reversedPay gBolt (dummyProposal gBolt .spell bolt (ManaCost.ofGeneric 1)) &&
      (mshRuling 697).comment.contains "isn't a nonartifact spell" &&
      (mshRuling 699).comment.contains "isn't a nonartifact spell"

#guard vibraniumSpendNotOnNonartifactOk

/-!
## 728 — Maximum hand size is checked only in cleanup
-/

def maxHandSizeCleanupOnlyOk : Bool :=
  let gTen := addPermanent afterDraw theTenRings ⟨0⟩ ⟨0⟩
  let gMarvel := addPermanent afterDraw msMarvelKamalaKhan ⟨0⟩ ⟨0⟩
  let gBoth := addPermanent gTen msMarvelKamalaKhan ⟨0⟩ ⟨0⟩
  let gRev := addPermanent (addPermanent afterDraw msMarvelKamalaKhan ⟨0⟩ ⟨0⟩)
    theTenRings ⟨0⟩ ⟨0⟩
  gTen.effectiveMaxHandSize ⟨0⟩ == 10 &&
    gMarvel.effectiveMaxHandSize ⟨0⟩ == 10000 &&
    gBoth.effectiveMaxHandSize ⟨0⟩ == 10000 &&
    gRev.effectiveMaxHandSize ⟨0⟩ == 10 &&
    (let g := addToHand afterDraw grizzlyBears ⟨0⟩
     let g := addToHand g grayOgre ⟨0⟩
     let g := addToHand g lightningBolt ⟨0⟩
     let before := (g.player ⟨0⟩).hand.size
     let gMain := g.discardToMaxHandSize
     let gKeep := addToHand gTen grizzlyBears ⟨0⟩
     let gKeep := addToHand gKeep grayOgre ⟨0⟩
     let gKeep := addToHand gKeep lightningBolt ⟨0⟩
     before > 7 &&
       (gMain.player ⟨0⟩).hand.size == 7 &&
       (gKeep.discardToMaxHandSize.player ⟨0⟩).hand.size == before) &&
    (mshRuling 728).comment.contains "cleanup step" &&
    (mshRuling 536).comment.contains "maximum hand size"

#guard maxHandSizeCleanupOnlyOk

/-- Ruling 640: Ms. Marvel's granted set-power overwrites a previous set P/T. -/
def msMarvelOverwritesSetPowerOk : Bool :=
  let g := addPermanent afterDraw msMarvelKamalaKhan ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Ms. Marvel, Kamala Khan"
  let g := g.setObject { o with
    status := { o.status with
      setBasePT := some (8, 4)
      grantedStaticAbilities := #[.powerEqualCardsInHand] } }
  let o := namedPermanent g "Ms. Marvel, Kamala Khan"
  let fromHand := Int.ofNat (g.player ⟨0⟩).hand.size
  g.power o == fromHand + (o.status.plusOnePlusOne : Int) &&
    (mshRuling 640).comment.contains "overwrite any previous effects"

#guard msMarvelOverwritesSetPowerOk

/-!
## Card-specific engine matches (remaining unique MSH rulings)
-/

def docSamsonExtraCountersOk : Bool :=
  let g := addPermanent afterDraw docSamsonSuperPsychiatrist ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.addPlusOnePlusOneTo bears 1
  (namedPermanent g "Grizzly Bears").status.plusOnePlusOne == 2 &&
    (let g2 := addPermanent g docSamsonSuperPsychiatrist ⟨0⟩ ⟨0⟩
     let b := namedPermanent g2 "Grizzly Bears"
     let g2 := g2.addPlusOnePlusOneTo b 1
     (namedPermanent g2 "Grizzly Bears").status.plusOnePlusOne == 5) &&
    (mshRuling 517).comment.contains "that many plus one" &&
    (mshRuling 576).comment.contains "two or more effects" &&
    (mshRuling 590).comment.contains "two Doc Samsons"

#guard docSamsonExtraCountersOk

def namorPowerAllZonesOk : Bool :=
  let g := addPermanent afterDraw namorTheSubMariner ⟨0⟩ ⟨0⟩
  let namor := namedPermanent g "Namor the Sub-Mariner"
  g.characteristicBasePower namor == 1 &&
    (let g := addPermanent g attumaAtlanteanWarlord ⟨0⟩ ⟨0⟩
     let namor := namedPermanent g "Namor the Sub-Mariner"
     g.characteristicBasePower namor == 2 &&
       (let (g, _) := g.move namor.id (.graveyard ⟨0⟩) none
        let gy := namedGraveyardCard g ⟨0⟩ "Namor the Sub-Mariner"
        g.characteristicBasePower gy == 1)) &&
    (mshRuling 641).comment.contains "works in all zones"

#guard namorPowerAllZonesOk

def superAdaptoidPowerAllZonesOk : Bool :=
  let g := addPermanent afterDraw superAdaptoid ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Super-Adaptoid"
  g.power o == 1 &&
    (mshRuling 642).comment.contains "works in all zones"

#guard superAdaptoidPowerAllZonesOk

def iAmIronManSetsPTOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let g := g.applyEffect ⟨0⟩ (Effect.becomeArtifactCreature44Flying)
    #[Target.permanent host.id]
  let o := namedPermanent g "Grizzly Bears"
  g.power o == 4 && g.toughness o == 4 &&
    o.isCreature && o.types.any (· == .artifact) &&
    (mshRuling 482).comment.contains "overwrite any previous effects" &&
    (mshRuling 488).comment.contains "doesn't count as \"crewing\"" &&
    (mshRuling 442).comment.contains "artifact creature"

#guard iAmIronManSetsPTOk

def frozenInIceCantUntapOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g frozenInIce ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let aura := namedPermanent g "Frozen in Ice"
  let g := g.attachSourceTo aura host
  let g := g.mapObjectStatus (namedPermanent g "Grizzly Bears")
    (fun s => { s with tapped := true })
  let host := namedPermanent g "Grizzly Bears"
  g.hostCantBecomeUntapped host &&
    (let g := g.applyPermanentAction host PermanentAction.untap
     (namedPermanent g "Grizzly Bears").status.tapped &&
       logContains g "can't become untapped") &&
    (mshRuling 518).comment.contains "won't untap" &&
    (mshRuling 554).comment.contains "can't be paid"

#guard frozenInIceCantUntapOk

def spiderWomanCantUntapOk : Bool :=
  let g := addPermanent afterDraw spiderWomanSecretAgent ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let wasp := namedPermanent g "Spider-Woman, Secret Agent"
  let host := namedPermanent g "Grizzly Bears"
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterTapOppCantUntapWhileControl)
    (some wasp.id) #[Target.permanent host.id]
  let host := namedPermanent g "Grizzly Bears"
  host.status.tapped && g.hostCantBecomeUntapped host &&
    (mshRuling 519).comment.contains "won't untap" &&
    (mshRuling 555).comment.contains "can't be paid"

#guard spiderWomanCantUntapOk

def hulklingGreaterStatOk : Bool :=
  let g := mshEnter afterDraw hulklingBurgeoningBruiser
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  let giant := namedPermanent g "Hill Giant"
  let g := g.afterPermanentEnters giant
  let hulkling := namedPermanent g "Hulkling, Burgeoning Bruiser"
  let fires := g.waitingTriggers.any (fun t =>
    t.source.name == "Hulkling, Burgeoning Bruiser")
  let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchHulklingCompare)
    (some hulkling.id) #[Target.permanent giant.id]
  (namedPermanent g "Hulkling, Burgeoning Bruiser").status.plusOnePlusOne == 1 &&
    fires &&
    (mshRuling 509).comment.contains "+1/+1 counters on it" &&
    (mshRuling 680).comment.contains "power to power" &&
    (mshRuling 684).comment.contains "won't trigger at all"

#guard hulklingGreaterStatOk

def hulklingSmallerDoesNotTriggerOk : Bool :=
  let g := mshEnter afterDraw hulklingBurgeoningBruiser
  let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
  let bot := namedPermanent g "Aerial Doombot"
  let g := g.afterPermanentEnters bot
  !g.waitingTriggers.any (fun t =>
    t.source.name == "Hulkling, Burgeoning Bruiser") &&
    (mshRuling 684).comment.contains "neither stat"

#guard hulklingSmallerDoesNotTriggerOk

def wolverineHealsOtherDamageOk : Bool :=
  let g := addPermanent afterDraw wolverineFierceFighter ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Wolverine, Fierce Fighter"
  let g := g.mapObjectStatus o (fun s => { s with damage := 3 })
  let o := namedPermanent g "Wolverine, Fierce Fighter"
  let g := g.markDamageOn o 2 "Wolverine is dealt 2 damage"
  (namedPermanent g "Wolverine, Fierce Fighter").status.damage == 2 &&
    (mshRuling 668).comment.contains "remove all damage" &&
    (mshRuling 692).comment.contains "replacement effect"

#guard wolverineHealsOtherDamageOk

def shieldRemovesOneOk : Bool :=
  let g := addPermanent afterDraw captainAmericaSuperSoldier ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Captain America, Super-Soldier"
  let g := g.setObject { o with status := { o.status with shield := 2 } }
  let o := namedPermanent g "Captain America, Super-Soldier"
  let g := g.markDamageOn o 5 "Cap is dealt 5 damage"
  let o := namedPermanent g "Captain America, Super-Soldier"
  o.status.shield == 1 && o.status.damage == 0 &&
    (mshRuling 515).comment.contains "only one shield counter" &&
    (mshRuling 424).comment.contains "not keyword counters" &&
    (mshRuling 626).comment.contains "isn't the same as regenerating" &&
    (mshRuling 633).comment.contains "sacrificing"

#guard shieldRemovesOneOk

def shieldUnpreventableStillRemovesOk : Bool :=
  let g := addPermanent afterDraw captainAmericaSuperSoldier ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Captain America, Super-Soldier"
  let g := g.setObject { o with status := { o.status with shield := 1 } }
  let o := namedPermanent g "Captain America, Super-Soldier"
  let g := g.markDamageOn o 3 "unpreventable" (unpreventable := true)
  let o := namedPermanent g "Captain America, Super-Soldier"
  o.status.shield == 0 && o.status.damage == 3 &&
    (mshRuling 516).comment.contains "unpreventable damage" &&
    (mshRuling 434).comment.contains "unpreventable damage"

#guard shieldUnpreventableStillRemovesOk

def powerUpStillHappensIfSourceLeftOk : Bool :=
  let g := addPermanent afterDraw whiteTigerAvaAyala ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "White Tiger, Ava Ayala"
  let (g, _) := g.move o.id (.graveyard ⟨0⟩) none
  let g := g.applyAbilityEffect ⟨0⟩
    (Effect.plusOneAndCreateTigerGod) #[] (some o.id)
  g.battlefield.any (fun x => x.name == "The Tiger God") &&
    (mshRuling 690).comment.contains "you'll still create The Tiger God" &&
    (mshRuling 653).comment.contains "you'll still create" &&
    (mshRuling 670).comment.contains "You'll create" &&
    (mshRuling 613).comment.contains "each opponent will still discard"

#guard powerUpStillHappensIfSourceLeftOk

def doublePowerAndToughnessOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let p0 := g.power host
  let t0 := g.toughness host
  let g := g.applyEffect ⟨0⟩ (Effect.doublePowerAndToughness)
    #[Target.permanent host.id]
  let o := namedPermanent g "Grizzly Bears"
  g.power o == p0 + p0 && g.toughness o == t0 + t0 &&
    (mshRuling 666).comment.contains "gets +X/+Y" &&
    (mshRuling 667).comment.contains "gets +X/+Y"

#guard doublePowerAndToughnessOk

def hydraulicHelperRestrictedBlueOk : Bool :=
  let g := addPermanent afterDraw hydraulicHelper ⟨0⟩ ⟨0⟩
  let helper := namedPermanent g "Hydraulic Helper"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.addBlueCantNonartifact) #[] (some helper.id)
  let p := (g.player ⟨0⟩).manaPool
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let (gArt, artSpell) := g.allocObject theMindStone ⟨0⟩ .stack (some ⟨0⟩)
  let (gBolt, bolt) := g.allocObject lightningBolt ⟨0⟩ .stack (some ⟨0⟩)
  p.cantNonartifactBlue == 1 &&
    !p.canPay (ManaCost.ofColor .blue) &&
    p.canPay (ManaCost.ofColor .blue) false false false false true &&
    paidOk g (dummyProposal g .activatedAbility bears (ManaCost.ofColor .blue)) &&
    paidOk gArt (dummyProposal gArt .spell artSpell (ManaCost.ofColor .blue)) &&
    reversedPay gBolt (dummyProposal gBolt .spell bolt (ManaCost.ofColor .blue)) &&
    (mshRuling 697).comment.contains "isn't a nonartifact spell"

#guard hydraulicHelperRestrictedBlueOk

def copyKeepsChosenXOk : Bool :=
  let (g, src) := afterDraw.allocObject photonBlastBarrage ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.setObject { src with chosenX := some 4 }
  let g := g.copyStackSpell (g.object! src.id) ⟨0⟩
  let copies := g.objects.filter (fun o =>
    o.name == "Photon Blast Barrage" && o.zone == .stack && o.isCopy)
  copies.size == 1 && copies[0]!.chosenX == some 4 &&
    (mshRuling 467).comment.contains "same target as the original" &&
    (mshRuling 560).comment.contains "same targets unless" &&
    (mshRuling 646).comment.contains "same targets unless" &&
    (mshRuling 676).comment.contains "creates X copies" &&
    (mshRuling 620).comment.contains "creates copies even if" &&
    (mshRuling 403).comment.contains "division and number of targets" &&
    (mshRuling 405).comment.contains "same mode or modes"

#guard copyKeepsChosenXOk

def capLivingLegendFirstTapUntapsOk : Bool :=
  let g := addPermanent afterDraw captainAmericaLivingLegend ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.applyPermanentAction bears PermanentAction.tap
  let bears := namedPermanent g "Grizzly Bears"
  bears.status.tapped && bears.status.becameTappedThisTurn &&
    g.waitingTriggers.any (fun t =>
      t.source.name == "Captain America, Living Legend") &&
    (let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchFirstTapUntap)
       none #[]
     !(namedPermanent g "Grizzly Bears").status.tapped) &&
    (mshRuling 457).comment.contains "became tapped earlier" &&
    (mshRuling 477).comment.contains "already tapped"

#guard capLivingLegendFirstTapUntapsOk

/-- Ruling 477: Hawkeye's Bow triggers only when the equipped creature
actually changes from untapped to tapped. -/
def hawkeyeBowBecomesTappedOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addAttachedAura g hawkeyeSBow (namedPermanent g "Grizzly Bears") ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let gTap := g.applyPermanentAction host PermanentAction.tap
  let fired :=
    gTap.waitingTriggers.any (fun t => t.source.name == "Hawkeye's Bow")
  let host := namedPermanent gTap "Grizzly Bears"
  let gAgain := gTap.applyPermanentAction host PermanentAction.tap
  let life1 := (g.player ⟨1⟩).life
  let bow := namedPermanent gTap "Hawkeye's Bow"
  let gDmg :=
    gTap.applyTriggeredAbility ⟨0⟩ (.onWatch Effect.watchEquippedTappedDamage)
      (some bow.id)
  fired &&
    gAgain.waitingTriggers.size == gTap.waitingTriggers.size &&
    gAgain.log.any (fun s => mentions s "already tapped") &&
    (gDmg.player ⟨1⟩).life + 1 == life1 &&
    (mshRuling 477).comment.contains "already tapped"

#guard hawkeyeBowBecomesTappedOk

/-- Rulings 98 / 110 / 244–246 / 249 / 255 / 277: second-card triggers fire
even if the permanent entered after the first draw. -/
def secondCardDrawnAfterEnterOk : Bool :=
  let g := afterDraw.modifyPlayer ⟨0⟩ (fun pl => { pl with cardsDrawnThisTurn := 1 })
  let g := addPermanent g kangTemporalTyrant ⟨0⟩ ⟨0⟩
  let g := addPermanent g kidLoki ⟨0⟩ ⟨0⟩
  let g := g.draw ⟨0⟩ 1
  g.waitingTriggers.any (fun t => t.source.name == "Kang, Temporal Tyrant") &&
    g.waitingTriggers.any (fun t => t.source.name == "Kid Loki") &&
    (mshRuling 451).comment.contains "second card" &&
    (mshRuling 463).comment.contains "second card" &&
    (mshRuling 596).comment.contains "second card" &&
    (mshRuling 597).comment.contains "second card" &&
    (mshRuling 598).comment.contains "second card" &&
    (mshRuling 601).comment.contains "second card" &&
    (mshRuling 607).comment.contains "second card" &&
    (mshRuling 629).comment.contains "second card"

#guard secondCardDrawnAfterEnterOk

/-- Ruling 450: Kid Loki hexproof applies to creatures that got +1/+1 earlier. -/
def kidLokiHexproofAfterCountersOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.addPlusOnePlusOneTo bears 1
  let bears := namedPermanent g "Grizzly Bears"
  !g.hasHexproof bears &&
    (let g := addPermanent g kidLoki ⟨0⟩ ⟨0⟩
     let bears := namedPermanent g "Grizzly Bears"
     g.hasHexproof bears &&
       (mshRuling 450).comment.contains "Kid Loki")

#guard kidLokiHexproofAfterCountersOk

/-- Rulings 149 / 141: leave-before-resolve exile does nothing. -/
def leaveBeforeResolveExileOk : Bool :=
  let g := addPermanent afterDraw webUp ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let web := namedPermanent g "Web Up"
  let bears := namedPermanent g "Grizzly Bears"
  let (g, _) := g.move web.id (.graveyard ⟨0⟩) none
  let g := g.applyTriggeredAbility ⟨0⟩ .onEnterExileOppNonlandUntilLeaves
    (some web.id) #[Target.permanent bears.id]
  onBattlefield g "Grizzly Bears" &&
    !g.objects.any (fun o => o.name == "Grizzly Bears" && o.zone == .exile) &&
    (let g := addPermanent afterDraw superVillainLockup ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
     let lock := namedPermanent g "Super Villain Lockup"
     let bears := namedPermanent g "Grizzly Bears"
     let (g, _) := g.move lock.id (.graveyard ⟨0⟩) none
     let g := g.applyTriggeredAbility ⟨0⟩ .onEnterExileOppTappedUntilLeaves
       (some lock.id) #[Target.permanent bears.id]
     onBattlefield g "Grizzly Bears" &&
       !g.objects.any (fun o => o.name == "Grizzly Bears" && o.zone == .exile)) &&
    (mshRuling 502).comment.contains "won't be exiled" &&
    (mshRuling 494).comment.contains "won't be exiled"

#guard leaveBeforeResolveExileOk

/-- Ruling 485 / 204 / 225: Cloak and Dagger still reveal if they left. -/
def cloakAndDaggerRevealIfLeftOk : Bool :=
  let g := addToHand afterDraw lightningBolt ⟨1⟩
  let g := addPermanent g cloakAndDaggerEntwined ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let cloak := namedPermanent g "Cloak and Dagger, Entwined"
  let bears := namedPermanent g "Grizzly Bears"
  let (g, _) := g.move cloak.id (.graveyard ⟨0⟩) none
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterRevealHandExileUntilLeaves)
    (some cloak.id) #[Target.player ⟨1⟩, Target.permanent bears.id]
  logContains g "reveals their hand" &&
    onBattlefield g "Grizzly Bears" &&
    !g.objects.any (fun o => o.name == "Grizzly Bears" && o.zone == .exile) &&
    (mshRuling 485).comment.contains "still reveal" &&
    (mshRuling 577).comment.contains "still do as much as it can"

#guard cloakAndDaggerRevealIfLeftOk

/-- Rulings 140 / 325 / 329: Secret Invasion leaving skips exile and the copy. -/
def secretInvasionLeaveOk : Bool :=
  let g := addPermanent afterDraw secretInvasion ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  let aura := namedPermanent g "Secret Invasion"
  let host := namedPermanent g "Grizzly Bears"
  let tgt := namedPermanent g "Hill Giant"
  let g := g.attachSourceTo aura host
  let (g, _) := g.move aura.id (.graveyard ⟨0⟩) none
  let g := g.applyTriggeredAbility ⟨0⟩ .onEnterExileOtherCopyEnchanted
    (some aura.id) #[Target.permanent tgt.id]
  onBattlefield g "Hill Giant" &&
    onBattlefield g "Grizzly Bears" &&
    (namedPermanent g "Grizzly Bears").printed.name == "Grizzly Bears" &&
    (mshRuling 493).comment.contains "won't be exiled"

#guard secretInvasionLeaveOk

/-- Rulings 121 / 200 / 201 / 322: Absorbing Man copies printed values, no ETB. -/
def absorbingManCopyOk : Bool :=
  let g := addPermanent afterDraw absorbingMan ⟨0⟩ ⟨0⟩
  let g := addPermanent g doctorDoom ⟨0⟩ ⟨0⟩
  let am := namedPermanent g "Absorbing Man"
  let doom := namedPermanent g "Doctor Doom"
  let before := g.waitingTriggers.size
  let g := g.applyModeledTrigger ⟨0⟩ (.onStep Effect.stepCopyAbsorbingMan) (some am.id)
    #[Target.permanent doom.id]
  let am := namedPermanent g "Absorbing Man"
  am.printed.name == "Absorbing Man" &&
    am.printed.power == some 4 &&
    am.printed.types.any (· == .creature) &&
    am.copyRestore.isSome &&
    am.copyUntilNextTurn &&
    g.waitingTriggers.size == before &&
    (mshRuling 474).comment.contains "exactly what was printed" &&
    (mshRuling 674).comment.contains "neither entering nor leaving"

#guard absorbingManCopyOk

/-- Rulings 122 / 196 / 198 / 326: Taskmaster copies a creature or graveyard card. -/
def taskmasterCopyOk : Bool :=
  let g := addPermanent afterDraw taskmasterMercenaryMimic ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  let tm := namedPermanent g "Taskmaster, Mercenary Mimic"
  let giant := namedPermanent g "Hill Giant"
  let g := g.applyModeledTrigger ⟨0⟩ (.onStep Effect.stepCopyTaskmaster) (some tm.id)
    #[Target.permanent giant.id]
  let tm := namedPermanent g "Taskmaster, Mercenary Mimic"
  tm.printed.name == "Taskmaster, Mercenary Mimic" &&
    tm.printed.power == hillGiant.power &&
    tm.copyUntilNextTurn &&
    (let g2 := addPermanent afterDraw taskmasterMercenaryMimic ⟨0⟩ ⟨0⟩
     let g2 := addPermanent g2 hillGiant ⟨1⟩ ⟨1⟩
     let giant := namedPermanent g2 "Hill Giant"
     let (g2, _) := g2.move giant.id (.graveyard ⟨1⟩) none
     let gy := namedGraveyardCard g2 ⟨1⟩ "Hill Giant"
     let tm := namedPermanent g2 "Taskmaster, Mercenary Mimic"
     let g2 := g2.applyModeledTrigger ⟨0⟩ (.onStep Effect.stepCopyTaskmaster)
       (some tm.id) #[Target.card gy.id]
     (namedPermanent g2 "Taskmaster, Mercenary Mimic").printed.power ==
       hillGiant.power) &&
    (mshRuling 475).comment.contains "exactly what was printed" &&
    (mshRuling 678).comment.contains "neither entering nor leaving"

#guard taskmasterCopyOk

/-- Rulings 120 / 188 / 193 / 194 / 330: Shuri copies until EOT and isn't legendary. -/
def shuriCopyUntilEotOk : Bool :=
  let g := addPermanent afterDraw shuriWakandanInventor ⟨0⟩ ⟨0⟩
  let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
  let g := addPermanent g sHIELDDeploymentDrone ⟨0⟩ ⟨0⟩
  let destId := (namedPermanent g "Aerial Doombot").id
  let src := namedPermanent g "S.H.I.E.L.D. Deployment Drone"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.copyArtifactYouControlNotLegendary)
    #[Target.permanent destId, Target.permanent src.id]
  let dest := g.object! destId
  dest.printed.name == "S.H.I.E.L.D. Deployment Drone" &&
    dest.copyUntilEot &&
    !dest.printed.supertypes.any (· == .legendary) &&
    dest.copyRestore.isSome &&
    (dest.copyRestore.getD dest.printed).name == "Aerial Doombot" &&
    (let g := g.clearEOT
     (g.object! destId).printed.name == "Aerial Doombot") &&
    (let g2 := addPermanent afterDraw shuriWakandanInventor ⟨0⟩ ⟨0⟩
     let g2 := addPermanent g2 aerialDoombot ⟨0⟩ ⟨0⟩
     let dest := namedPermanent g2 "Aerial Doombot"
     let destName := dest.printed.name
     let g2 := g2.applyAbilityEffect ⟨0⟩ (Effect.copyArtifactYouControlNotLegendary)
       #[Target.permanent dest.id]
     (g2.object! dest.id).printed.name == destName) &&
    (mshRuling 473).comment.contains "exactly what was printed" &&
    (mshRuling 540).comment.contains "won't have any effect" &&
    (mshRuling 682).comment.contains "neither entering nor leaving"

#guard shuriCopyUntilEotOk

/-- Rulings 197 / 199 / 325: Secret Invasion copies until the Aura leaves. -/
def secretInvasionCopyOk : Bool :=
  let g := addPermanent afterDraw secretInvasion ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  let aura := namedPermanent g "Secret Invasion"
  let host := namedPermanent g "Grizzly Bears"
  let tgt := namedPermanent g "Hill Giant"
  let g := g.attachSourceTo aura host
  let g := g.applyTriggeredAbility ⟨0⟩ .onEnterExileOtherCopyEnchanted
    (some aura.id) #[Target.permanent tgt.id]
  let host := g.object! host.id
  host.copyRestore.isSome &&
    (host.copyRestore.getD host.printed).name == "Grizzly Bears" &&
    host.printed.name == "Hill Giant" &&
    (let aura := namedPermanent g "Secret Invasion"
     let (g, _) := g.move aura.id (.graveyard ⟨0⟩) none
     (namedPermanent g "Grizzly Bears").printed.name == "Grizzly Bears") &&
    (mshRuling 677).comment.contains "exactly what was printed" &&
    (mshRuling 681).comment.contains "neither entering nor leaving"

#guard secretInvasionCopyOk

/-- Rulings 95 / 142 / 160: She-Hulk may deal the total even if she left; once. -/
def sheHulkDamageOnceOk : Bool :=
  let g := addPermanent afterDraw theSensationalSheHulk ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  let she := namedPermanent g "The Sensational She-Hulk"
  let bears := namedPermanent g "Grizzly Bears"
  let giant := namedPermanent g "Hill Giant"
  let g := g.markDamageOn bears 3 "Bears are dealt 3 damage"
  g.waitingTriggers.any (fun t =>
    t.source.name == "The Sensational She-Hulk") &&
    (let (g, _) := g.move she.id (.graveyard ⟨0⟩) none
     let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchSheHulkRedirectOnce)
       (some she.id) #[Target.permanent giant.id]
       "The Sensational She-Hulk" (some 3)
     let giant := namedPermanent g "Hill Giant"
     giant.status.damage == 3 &&
       g.sheHulkDamageUsedThisTurn &&
       (let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchSheHulkRedirectOnce)
          (some she.id) #[Target.permanent giant.id]
          "The Sensational She-Hulk" (some 5)
        (namedPermanent g "Hill Giant").status.damage == 3 &&
          logContains g "no effect")) &&
    (mshRuling 448).comment.contains "won't trigger again that turn" &&
    (mshRuling 495).comment.contains "may still have her deal damage" &&
    (mshRuling 512).comment.contains "total amount of damage"

#guard sheHulkDamageOnceOk

/-- Rulings 34 / 40 / 47 / 61 / 62 / 302: copying a stack ability is not
casting and keeps the same source and X. -/
def copyStackAbilityOk : Bool :=
  let g := addPermanent afterDraw aerialDoombot ⟨0⟩ ⟨0⟩
  let src := namedPermanent g "Aerial Doombot"
  let (g, ab) := g.allocStackAbility src ⟨0⟩
    (triggeredAbility := some (.onEnterDraw 1)) (lastKnownPower := some 4)
  let g := g.setObject { ab with chosenX := some 2 }
  let g := g.putStackEntry ⟨0⟩ ab.id
  let origId := ab.id
  let g := g.copyStackAbility (g.object! origId) ⟨0⟩
  let copies := g.objects.filter (fun o =>
    o.zone == .stack && o.isCopy && o.sourceId == some src.id)
  copies.size == 1 &&
    copies[0]!.chosenX == some 2 &&
    copies[0]!.lastKnownPower == some 4 &&
    copies[0]!.triggeredAbility.isSome &&
    g.stack.size == 2 &&
    g.stack.back!.objectId == copies[0]!.id &&
    (mshRuling 389).comment.contains "won't apply to copying" &&
    (mshRuling 394).comment.contains "won't cause abilities that trigger" &&
    (mshRuling 401).comment.contains "same value of X" &&
    (mshRuling 414).comment.contains "same targets as the ability" &&
    (mshRuling 415).comment.contains "resolve before the original" &&
    (mshRuling 654).comment.contains "same as the source of the original"

#guard copyStackAbilityOk

/-- Ruling 449: Worlds Within Worlds exiles creatures, then hand creatures
enter, then the exiled cards return to hands. -/
def worldsWithinWorldsOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  let g := addToHand g aerialDoombot ⟨0⟩
  let (g, spell) := g.allocObject worldsWithinWorlds ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.applyWorldsWithinWorlds ⟨0⟩ (some spell.id)
  g.battlefield.any (fun o => o.name == "Aerial Doombot") &&
    !g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    !g.battlefield.any (fun o => o.name == "Hill Giant") &&
    (g.player ⟨0⟩).hand.any (fun id => (g.object! id).name == "Grizzly Bears") &&
    (g.player ⟨1⟩).hand.any (fun id => (g.object! id).name == "Hill Giant") &&
    (match g.findObject? spell.id with
     | some o => o.zone == .exile
     | none =>
       g.objects.any (fun o => o.name == "Worlds Within Worlds" && o.zone == .exile)) &&
    (mshRuling 449).comment.contains "Worlds Within Worlds"

#guard worldsWithinWorldsOk

/-- Ruling 484: Captain America's attack pump uses last-known toughness. -/
def capWingsLastKnownToughnessOk : Bool :=
  let g := addPermanent afterDraw captainAmericaWingsOfFreedom ⟨0⟩ ⟨0⟩
  let g := addPermanent g sheHulkJadeDefender ⟨0⟩ ⟨0⟩
  let cap := namedPermanent g "Captain America, Wings of Freedom"
  let g := g.mapObjectStatus cap (fun s => { s with pump := (0, 4) })
  let cap := namedPermanent g "Captain America, Wings of Freedom"
  let tw := g.toughness cap
  let she0 := g.toughness (namedPermanent g "She-Hulk, Jade Defender")
  let (g, _) := g.move cap.id (.graveyard ⟨0⟩) none
  let g := g.applyTriggeredAbility ⟨0⟩
    (.onAttackOthersOfSubtypeGetEqualToughness "Hero") (some cap.id)
    #[] #[] none (some tw)
  g.toughness (namedPermanent g "She-Hulk, Jade Defender") == she0 + tw &&
    (mshRuling 484).comment.contains "last existed on the battlefield" &&
    (mshRuling 662).comment.contains "determined only once"

#guard capWingsLastKnownToughnessOk

/-- Ruling 500 / 321: Viv Vision draws using last-known power if she left. -/
def vivVisionLastKnownPowerOk : Bool :=
  let g := addPermanent afterDraw vivVisionTeenSynthezoid ⟨0⟩ ⟨0⟩
  let viv := namedPermanent g "Viv Vision, Teen Synthezoid"
  let g := g.addPlusOnePlusOneTo viv 2
  let viv := namedPermanent g "Viv Vision, Teen Synthezoid"
  let pw := g.power viv
  let hand0 := (g.player ⟨0⟩).hand.size
  let (g, _) := g.move viv.id (.graveyard ⟨0⟩) none
  let g := g.applyModeledTrigger ⟨0⟩ (.onThisAttack Effect.thisAttackDrawIfPower4) (some viv.id)
    #[] "Viv Vision" (some pw)
  pw >= 4 &&
    (g.player ⟨0⟩).hand.size == hand0 + 1 &&
    (mshRuling 500).comment.contains "last existed on the battlefield" &&
    (mshRuling 673).comment.contains "checks Viv Vision's power only as it resolves"

#guard vivVisionLastKnownPowerOk

/-- Ruling 501: War Machine's combat pump uses last-known power. -/
def warMachineLastKnownPowerOk : Bool :=
  let g := addPermanent afterDraw warMachineLegacyOfIron ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let wm := namedPermanent g "War Machine, Legacy of Iron"
  let g := g.addPlusOnePlusOneTo wm 3
  let wm := namedPermanent g "War Machine, Legacy of Iron"
  let pw := g.power wm
  let bears := namedPermanent g "Grizzly Bears"
  let p0 := g.power bears
  let (g, _) := g.move wm.id (.graveyard ⟨0⟩) none
  let g := g.applyTriggeredAbility ⟨0⟩ .onCombatAnotherGetsSourcePower (some wm.id)
    #[Target.permanent bears.id] #[] (some pw)
  g.power (namedPermanent g "Grizzly Bears") == p0 + pw &&
    (mshRuling 501).comment.contains "last existed on the battlefield" &&
    (mshRuling 660).comment.contains "calculated only once"

#guard warMachineLastKnownPowerOk

/-- Leader's combat trigger connives the targeted creature, not Leader. -/
def leaderCombatConniveTargetsOtherOk : Bool :=
  let g := addPermanent afterDraw leaderSuperGenius ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addToHand g lightningBolt ⟨0⟩
  let leader := namedPermanent g "Leader, Super-Genius"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.applyTriggeredAbility ⟨0⟩ .onCombatTargetYouControlConnives (some leader.id)
    #[Target.permanent bears.id]
  let g := discardNamed g ⟨0⟩ "Lightning Bolt"
  (namedPermanent g "Grizzly Bears").status.plusOnePlusOne == 1 &&
    (namedPermanent g "Leader, Super-Genius").status.plusOnePlusOne == 0

#guard leaderCombatConniveTargetsOtherOk

/-- Alien Invasion creates a hasty Alien, then grows later tokens from invasion. -/
def alienInvasionCombatTokenOk : Bool :=
  let g := addPermanent afterDraw alienInvasion ⟨0⟩ ⟨0⟩
  let src := namedPermanent g "Alien Invasion"
  let g := g.applyTriggeredAbility ⟨0⟩ .onCombatCreateAlienPerInvasion (some src.id)
  let tok := namedPermanent g "Alien"
  let firstOk :=
    tok.printed.isToken && tok.status.plusOnePlusOne == 0 &&
      tok.printed.keywords.haste &&
      tok.staticAbilities.contains .attacksEachCombatIfAble &&
      (namedPermanent g "Alien Invasion").status.invasion == 1
  let src := namedPermanent g "Alien Invasion"
  let g := g.applyTriggeredAbility ⟨0⟩ .onCombatCreateAlienPerInvasion (some src.id)
  let aliens := g.battlefield.filter (fun o => o.name == "Alien")
  firstOk &&
    aliens.size == 2 &&
    aliens.any (fun o => o.status.plusOnePlusOne == 0) &&
    aliens.any (fun o => o.status.plusOnePlusOne == 1) &&
    (namedPermanent g "Alien Invasion").status.invasion == 2

#guard alienInvasionCombatTokenOk

/-- Iron Man may put Equipment from hand onto the battlefield attached to him. -/
def ironManCombatPutEquipmentOk : Bool :=
  let g := addPermanent afterDraw theInvincibleIronMan ⟨0⟩ ⟨0⟩
  let g := addToHand g hawkeyeSBow ⟨0⟩
  let iron := namedPermanent g "The Invincible Iron Man"
  let g := g.applyTriggeredAbility ⟨0⟩ .onCombatMayPutArtifactAttachEquipment
    (some iron.id)
  match g.pending with
  | .mayPutArtifactFromHand ⟨0⟩ hostId =>
    let bow := handCardNamed g ⟨0⟩ "Hawkeye's Bow"
    let g := mustApply g ⟨0⟩ (.cast bow.id)
    let bow := namedPermanent g "Hawkeye's Bow"
    hostId == iron.id &&
      bow.isOnBattlefield &&
      bow.attachedTo == some iron.id
  | _ => false

#guard ironManCombatPutEquipmentOk

/-- Iron Man may decline the optional put. -/
def ironManCombatDeclinePutOk : Bool :=
  let g := addPermanent afterDraw theInvincibleIronMan ⟨0⟩ ⟨0⟩
  let g := addToHand g hawkeyeSBow ⟨0⟩
  let iron := namedPermanent g "The Invincible Iron Man"
  let g := g.applyTriggeredAbility ⟨0⟩ .onCombatMayPutArtifactAttachEquipment
    (some iron.id)
  let g := mustApply g ⟨0⟩ .decline
  (handCardNamed g ⟨0⟩ "Hawkeye's Bow").zone == .hand ⟨0⟩ &&
    g.pending == .none &&
    g.log.any (fun s => mentions s "declines to put an artifact")

#guard ironManCombatDeclinePutOk

/-- Iron Man puts a non-Equipment artifact without attaching it. -/
def ironManCombatPutNonEquipmentOk : Bool :=
  let g := addPermanent afterDraw theInvincibleIronMan ⟨0⟩ ⟨0⟩
  let g := addToHand g theMindStone ⟨0⟩
  let iron := namedPermanent g "The Invincible Iron Man"
  let g := g.applyTriggeredAbility ⟨0⟩ .onCombatMayPutArtifactAttachEquipment
    (some iron.id)
  let stone := handCardNamed g ⟨0⟩ "The Mind Stone"
  let g := mustApply g ⟨0⟩ (.cast stone.id)
  let stone := namedPermanent g "The Mind Stone"
  stone.isOnBattlefield && stone.attachedTo.isNone

#guard ironManCombatPutNonEquipmentOk

/-- Ruling 490: Political Triumph still draws and counters if it left. -/
def politicalTriumphLeftOk : Bool :=
  let g := addPermanent afterDraw politicalTriumph ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let plan := namedPermanent g "Political Triumph"
  let hand0 := (g.player ⟨0⟩).hand.size
  let (g, _) := g.move plan.id (.graveyard ⟨0⟩) none
  let g := g.applyTriggeredAbility ⟨0⟩ .onFourthPlanDrawPlusOneEach (some plan.id)
  (g.player ⟨0⟩).hand.size == hand0 + 1 &&
    (namedPermanent g "Grizzly Bears").status.plusOnePlusOne == 1 &&
    (mshRuling 490).comment.contains "won't be able to sacrifice it"

#guard politicalTriumphLeftOk

/-- Ruling 492: Robot Domination still creates tokens if it left. -/
def robotDominationLeftOk : Bool :=
  let g := addPermanent afterDraw robotDomination ⟨0⟩ ⟨0⟩
  let plan := namedPermanent g "Robot Domination"
  let (g, _) := g.move plan.id (.graveyard ⟨0⟩) none
  let g := g.applyTriggeredAbility ⟨0⟩ .onThirdPlanCreateRobots (some plan.id)
  (g.battlefield.filter (fun o => o.name == "Robot Villain")).size == 3 &&
    (mshRuling 492).comment.contains "You'll create the Robot"

#guard robotDominationLeftOk

/-- Ruling 489: Jessica Jones exiles X using last-known power if she left. -/
def jessicaJonesLastKnownXOk : Bool :=
  let g := addPermanent afterDraw jessicaJonesPrivateEye ⟨0⟩ ⟨0⟩
  let jj := namedPermanent g "Jessica Jones, Private Eye"
  let g := g.addPlusOnePlusOneTo jj 1
  let jj := namedPermanent g "Jessica Jones, Private Eye"
  let pw := g.power jj
  let lib0 := (g.player ⟨0⟩).library.size
  let (g, _) := g.move jj.id (.graveyard ⟨0⟩) none
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.exileTopXPlayThisTurn) #[]
    (some jj.id) (some pw)
  (g.player ⟨0⟩).library.size == lib0 - pw.toNat &&
    (g.objects.filter (fun o =>
      o.zone == .exile && o.playPermission.isSome)).size == pw.toNat &&
    (mshRuling 489).comment.contains "last existed on the battlefield" &&
    (mshRuling 658).comment.contains "calculated only once"

#guard jessicaJonesLastKnownXOk

/-- Ruling 503: Whiplash drain uses last-known attached Equipment. -/
def whiplashLastKnownEquipmentOk : Bool :=
  let g := addPermanent afterDraw whiplashVengefulEngineer ⟨0⟩ ⟨0⟩
  let g := addPermanent g captainAmericaSShield ⟨0⟩ ⟨0⟩
  let g := addPermanent g falconSWingHarness ⟨0⟩ ⟨0⟩
  let whip := namedPermanent g "Whiplash, Vengeful Engineer"
  let eq1 := namedPermanent g "Captain America's Shield"
  let eq2 := namedPermanent g "Falcon's Wing Harness"
  let g := g.attachSourceTo eq1 whip
  let g := g.attachSourceTo eq2 (g.object! whip.id)
  let n := g.attachedEquipmentCount (g.object! whip.id)
  let life0 := (g.player ⟨1⟩).life
  let you0 := (g.player ⟨0⟩).life
  let (g, _) := g.move (namedPermanent g "Whiplash, Vengeful Engineer").id
    (.graveyard ⟨0⟩) none
  let g := g.applyModeledTrigger ⟨0⟩ (.onThisAttack Effect.thisAttackEquippedDrain) (some whip.id)
    #[] "Whiplash" (some (Int.ofNat n))
  n == 2 &&
    (g.player ⟨1⟩).life + n == life0 &&
    (g.player ⟨0⟩).life == you0 + n &&
    (mshRuling 503).comment.contains "last existed on the battlefield" &&
    (mshRuling 661).comment.contains "calculated only once"

#guard whiplashLastKnownEquipmentOk

/-- Rulings 359 / 367: first reflexive ability has no targets; the second does. -/
def mshReflexiveNoTargetFirstOk : Bool :=
  let g := addPermanent afterDraw bullseyeDeathDealer ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let b := namedPermanent g "Bullseye, Death Dealer"
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterMaySacOrDiscardNonlandThenDamage) (some b.id)
  (namedPermanent g "Grizzly Bears").status.damage == 0 &&
    g.pendingMshReflexive.isSome &&
    logContains g "reflexive" &&
    (let bears := namedPermanent g "Grizzly Bears"
     let g := g.applyModeledReflexive #[Target.permanent bears.id]
     (namedPermanent g "Grizzly Bears").status.damage == 2) &&
    (let g := addPermanent afterDraw spiderManToTheRescue ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
     let sm := namedPermanent g "Spider-Man, To the Rescue"
     let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterMayTapThenGrantIndestructible) (some sm.id)
     (namedPermanent g "Spider-Man, To the Rescue").status.tapped &&
       g.pendingMshReflexive.isSome &&
       (let bears := namedPermanent g "Grizzly Bears"
        let g := g.applyModeledReflexive #[Target.permanent bears.id]
        (namedPermanent g "Grizzly Bears").status.untilEotKeywords.indestructible)) &&
    (mshRuling 711).comment.contains "reflexive" &&
    (mshRuling 719).comment.contains "reflexive"

#guard mshReflexiveNoTargetFirstOk

/-- Ruling 478: Hawkeye's first trigger has no modes; paying queues the second. -/
def hawkeyeReflexivePayOk : Bool :=
  let g := addPermanent afterDraw hawkeyeMasterMarksman ⟨0⟩ ⟨0⟩
  let hawk := namedPermanent g "Hawkeye, Master Marksman"
  let nonePaid :=
    g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchHawkeyeModes) (some hawk.id)
      #[] "Hawkeye" none
  !nonePaid.pendingMshReflexive.isSome &&
    (let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchHawkeyeModes) (some hawk.id)
       #[] "Hawkeye" (some (2 : Int))
     g.pendingMshReflexive.isSome &&
       g.pendingMshReflexivePaid == 2 &&
       (let life1 := (g.player ⟨1⟩).life
        let g := g.applyModeledReflexive #[Target.player ⟨1⟩]
        (g.player ⟨1⟩).life + 2 == life1)) &&
    (mshRuling 478).comment.contains "reflexive"

#guard hawkeyeReflexivePayOk

end Mtg.Engine.MshRulingTests
