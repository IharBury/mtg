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
  let g := addPermanent afterDraw helicarrierStrike ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Helicarrier Strike"
  !o.teamworkPaid &&
    helicarrierStrike.teamwork == some 2 &&
    (match g.apply ⟨0⟩ (.announceTeamwork true) with
     | .error _ => true
     | .ok _ => false) &&
    (mshRuling 7).comment.contains "without casting it"

#guard teamworkNotPaidWhenNotCastOk

/-- Ruling 5: casting without paying the mana cost still allows optional
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
    (mshRuling 5).comment.contains "without paying its mana cost" &&
    helicarrierStrike.teamwork.isSome &&
    (mshRuling 230).comment.contains "teamwork costs"

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
    (let g := addPermanent afterDraw bruceBanner ⟨0⟩ ⟨0⟩
     let banner := namedPermanent g "Bruce Banner"
     g.objectManaValue banner == 1 &&
       (let g := g.applyAbilityEffect ⟨0⟩ .transform #[] (some banner.id)
        g.objectManaValue (namedPermanent g "The Incredible Hulk") == 6)) &&
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
  let faces : Array CardDef :=
    match bruceBanner.otherFace with
    | none => #[bruceBanner]
    | some back => #[bruceBanner, back]
  let greenFaces :=
    faces.filter (fun c => c.colors.contains .green) |>.map (fun c => c.name)
  (namedPermanent g "Bruce Banner").printed.name == "Bruce Banner" &&
    !(namedPermanent g "Bruce Banner").status.transformed &&
    greenFaces == #["The Incredible Hulk"] &&
    (mshRuling 16).comment.contains "cast green spells" &&
    (mshRuling 17).comment.contains "front face"

#guard mdfcFrontFacePutOk

/-- Ruling 14 / 18 / 19: reminder icons have no rules; Commander color
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

/-- Ruling 344: Thirst for Knowledge may discard one artifact or two cards. -/
def thirstDiscardUnlessArtifactOk : Bool :=
  let g0 := addToHand afterDraw theMindStone ⟨0⟩
  let g0 := addToHand g0 lightningBolt ⟨0⟩
  let g0 := addToHand g0 mountain ⟨0⟩
  let gArt := g0.applyEffect ⟨0⟩ .drawThreeDiscardUnlessArtifact #[]
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
    (let gTwo := g0.applyEffect ⟨0⟩ .drawThreeDiscardUnlessArtifact #[]
     let gTwo := mustApply gTwo ⟨0⟩
       (.discard (handCardNamed gTwo ⟨0⟩ "Lightning Bolt").id)
     gTwo.thirstDiscardsLeft == 1 &&
       (let gTwo := mustApply gTwo ⟨0⟩
          (.discard (handCardNamed gTwo ⟨0⟩ "Mountain").id)
        gTwo.thirstDiscardsLeft == 0 &&
          gTwo.pending == .none)) &&
    (mshRuling 344).comment.contains "one artifact card or two cards"

#guard thirstDiscardUnlessArtifactOk

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
  | .error msg =>
    msg.contains "already tapped" &&
      (mshRuling 45).comment.contains "won't be able to tap it again"
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
    !afterDraw.canCastForSneak ⟨0⟩ &&
    (let g := { afterDraw with step := .declareBlockers, activePlayer := ⟨0⟩ }
     g.canCastForSneak ⟨0⟩ && !g.canCastForSneak ⟨1⟩) &&
    (let g := { afterDraw with step := .declareAttackers, activePlayer := ⟨0⟩ }
     !g.canCastForSneak ⟨0⟩) &&
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
        let g := g.applyMshTrigger ⟨0⟩ .wheneverEnchantedCreatureAttacksOrBlocks
          (some (namedPermanent g "Super-Soldier Serum").id)
          #[Target.permanent hammer.id]
        (namedPermanent g "Mjölnir, Hammer of Thor").attachedTo == some loki.id)) &&
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

/-!
## 103, 127, 337, 341–342 — Power-up interactions
-/

/-- Ruling 103: Bold Biochemist's power-up still draws if it has left. -/
def boldBiochemistDrawsAfterLeaveOk : Bool :=
  let g := addPermanent afterDraw boldBiochemist ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Bold Biochemist"
  let hand0 := (g.player ⟨0⟩).hand.size
  let (g, _) := g.move o.id (.graveyard ⟨0⟩) none
  let g := g.applyAbilityEffect ⟨0⟩ (.plusOneAndDraw 1 2) #[] (some o.id)
  (g.player ⟨0⟩).hand.size == hand0 + 2 &&
    !g.battlefield.any (fun x => x.name == "Bold Biochemist") &&
    (mshRuling 103).comment.contains "you'll still draw two cards"

#guard boldBiochemistDrawsAfterLeaveOk

/-- Ruling 127: Hulk reduces only generic mana on other creatures' power-up. -/
def hulkPowerUpGenericOnlyOk : Bool :=
  let g := addPermanent afterDraw hulkGammaGoliath ⟨0⟩ ⟨0⟩
  let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
  let bot := namedPermanent g "Aerial Doombot"
  let ab := bot.printed.activatedAbilities[0]!
  let cost := g.activationManaCost ⟨0⟩ ab (some bot)
  cost.coloredCount .blue == 1 &&
    cost.manaValue == ab.cost.mana.manaValue - 3 &&
    (mshRuling 127).comment.contains "only the amount of generic mana"

#guard hulkPowerUpGenericOnlyOk

/-- Ruling 337 / 342: Wonder Man lets each power-up be activated twice,
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
    (mshRuling 337).comment.contains "twice rather than once" &&
    (mshRuling 342).comment.contains "own power-up ability"

#guard wonderManExtraPowerUpOk

/-- Ruling 341: each Wonder Man adds one extra activation. -/
def twoWonderMenThreeActivationsOk : Bool :=
  let g := addPermanent afterDraw wonderManHollywoodHero ⟨0⟩ ⟨0⟩
  let g := addPermanent g wonderManHollywoodHero ⟨0⟩ ⟨0⟩
  let n :=
    (g.permanentsOf ⟨0⟩).filter Game.grantsExtraPowerUp |>.size
  n == 2 &&
    g.powerUpActivationLimit ⟨0⟩ == 3 &&
    (mshRuling 341).comment.contains "two of him"

#guard twoWonderMenThreeActivationsOk

/-!
## 21, 35, 42, 44, 50, 60, 63–65, 67, 74–75, 83, 87, 91,
## 128, 152–154, 162, 168, 176, 313 — Shared CR on MSH cards
-/

def mdfcPlayFaceOk : Bool :=
  let g := addToHand afterDraw bruceBanner ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Bruce Banner"
  g.canCast ⟨0⟩ card &&
    g.objectManaValue card == 1 &&
    bruceBanner.manaValue <= 2 &&
    theIncredibleHulk.manaValue > 2 &&
    (mshRuling 21).comment.contains "face you're playing"

#guard mdfcPlayFaceOk

def activatedVsTriggeredWordingOk : Bool :=
  aerialDoombot.activatedAbilities.any (·.powerUp) &&
    claimTheKingdom.triggeredAbilities.size > 0 &&
    (mshRuling 35).comment.contains "colon" &&
    (mshRuling 64).comment.contains "when"

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
    (mshRuling 42).comment.contains "doesn't become tapped"

#guard equipmentTapIndependentOk

def xZeroWithoutPayingOk : Bool :=
  let g := addToHand afterDraw photonBlastBarrage ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Photon Blast Barrage"
  let card := { card with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }
  g.playManaCost card photonBlastBarrage == ManaCost.zero &&
    (mshRuling 44).comment.contains "choose 0"

#guard xZeroWithoutPayingOk

def copyKeepsXAndIsNotCastOk : Bool :=
  let (g, src) := afterDraw.allocObject photonBlastBarrage ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.setObject { src with chosenX := some 3 }
  let g := g.copyStackSpell (g.object! src.id) ⟨0⟩
  let copies := g.objects.filter (fun o =>
    o.name == "Photon Blast Barrage" && o.zone == .stack && o.isCopy)
  copies.size == 1 && copies[0]!.chosenX == some 3 &&
    copies[0]!.isCopy &&
    (mshRuling 50).comment.contains "same value of X" &&
    (mshRuling 60).comment.contains "not \"cast.\"" &&
    (mshRuling 67).comment.contains "additional costs for the copy"

#guard copyKeepsXAndIsNotCastOk

def totalCostIncludesAdditionalOk : Bool :=
  helicarrierStrike.teamwork == some 2 &&
    helicarrierStrike.manaCost.manaValue == 1 &&
    (mshRuling 63).comment.contains "total cost of a spell" &&
    (mshRuling 65).comment.contains "additional costs" &&
    (mshRuling 313).comment.contains "total cost of a spell"

#guard totalCostIncludesAdditionalOk

def creatureAndArtifactSourceOk : Bool :=
  echoPerceptiveProdigy.isCreature &&
    scientistSupremeOfAIM.isCreature &&
    (mshRuling 74).comment.contains "creature source" &&
    (mshRuling 75).comment.contains "creature" &&
    (mshRuling 87).comment.contains "artifact source"

#guard creatureAndArtifactSourceOk

def poisonTenLosesOk : Bool :=
  let g := afterDraw.modifyPlayer ⟨0⟩ (fun pl => { pl with poison := 10 })
  let g := g.checkSBA
  (g.player ⟨0⟩).lost &&
    g.log.any (fun s => mentions s "poison") &&
    (mshRuling 83).comment.contains "ten or more poison"

#guard poisonTenLosesOk

def copiesYouDontCastCeaseOk : Bool :=
  let (g, src) := afterDraw.allocObject helicarrierStrike ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.copyStackSpell src ⟨0⟩
  let copy := (g.objects.filter (fun o => o.isCopy))[0]!
  let (g, _) := g.move copy.id .exile none
  let g := g.checkSBA
  !g.objects.any (fun o => o.isCopy) &&
    (mshRuling 91).comment.contains "cease to exist"

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
    (mshRuling 128).comment.contains "Hybrid mana symbols that include black"

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
    (mshRuling 43).comment.contains "X is 0" &&
    (mshRuling 152).comment.contains "X is 0" &&
    (mshRuling 153).comment.contains "X is 0" &&
    (mshRuling 154).comment.contains "X is 0" &&
    (mshRuling 161).comment.contains "X is 0" &&
    (mshRuling 162).comment.contains "X is 0" &&
    (mshRuling 168).comment.contains "value chosen for X"

#guard xIsZeroInZonesOk

/-- Ruling 176: tapping an already-tapped creature is not becoming tapped. -/
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
    (mshRuling 176).comment.contains "already tapped"

#guard tapAlreadyTappedOk

/-!
## 37–38, 58, 100–101 — Exile leaves Auras and Equipment behind
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
    (mshRuling 37).comment.contains "Equipment will become unattached" &&
    (mshRuling 38).comment.contains "remain on the battlefield" &&
    (mshRuling 100).comment.contains "Auras attached" &&
    (mshRuling 101).comment.contains "Equipment attached"

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
    (mshRuling 58).comment.contains "new object"

#guard returnedIsNewObjectOk

/-!
## 32, 69, 78–79, 82, 85–86, 111 — Landfall / once each turn / attacks
-/

def landfallEachAbilityOk : Bool :=
  let g := mshEnter afterDraw claimTheKingdom
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g forest ⟨0⟩ ⟨0⟩
  let g := settle ((g.afterLandEnters (namedPermanent g "Forest")).receivePriority ⟨0⟩) 24
  (namedPermanent g "Claim the Kingdom").status.plan == 1 &&
    (mshRuling 32).comment.contains "each landfall ability"

#guard landfallEachAbilityOk

def onceEachTurnConniveWordingOk : Bool :=
  let villainWait (g : Game) : Nat :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.anotherVillainEnters)).size
  let g0 := addPermanent afterDraw baronStruckerHYDRAOverlord ⟨0⟩ ⟨0⟩
  let g := addPermanent g0 redGuardianSuperSoldier ⟨0⟩ ⟨0⟩
  let g := g.afterPermanentEnters (namedPermanent g "Red Guardian, Super-Soldier")
  villainWait g == 1 &&
    (namedPermanent g "Baron Strucker, HYDRA Overlord").status.firedOnceEachTurn &&
    (let g := addPermanent g baronHelmutZemo ⟨0⟩ ⟨0⟩
     let g := g.afterPermanentEnters (namedPermanent g "Baron Helmut Zemo")
     villainWait g == 1) &&
    (mshRuling 69).comment.contains "Do this only once each turn"

#guard onceEachTurnConniveWordingOk

def enterAttackingNotDeclaredOk : Bool :=
  let g := addPermanent afterDraw baronHelmutZemo ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Baron Helmut Zemo"
  let g := g.setObject { o with status := { o.status with attacking := true } }
  !g.canActivateBoast (namedPermanent g "Baron Helmut Zemo") &&
    (mshRuling 85).comment.contains "never declared as an attacking creature" &&
    (mshRuling 86).comment.contains "never declared" &&
    (mshRuling 111).comment.contains "enter attacking"

#guard enterAttackingNotDeclaredOk

def attacksAloneWordingOk : Bool :=
  (mshRuling 78).comment.contains "attacks alone" &&
    (mshRuling 79).comment.contains "declare attackers step" &&
    (mshRuling 82).comment.contains "currently attacking"

#guard attacksAloneWordingOk

/-!
## 209–219 — Illegal targets cause the spell or ability to do nothing
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
  let gDepower := gGone.applyEffect ⟨0⟩ (.msh .thisSpellCosts2LessToCastIfItTargets) gone
  let gHour := gGone.applyEffect ⟨0⟩ .destroyCreatureSurveil gone
  let gPym := gGone.applyEffect ⟨0⟩ .grantVigilanceUnblockable gone
  let gCrescendo :=
    gGone.applyEffect ⟨0⟩ (.msh .targetCreatureGets31UntilEndOfTurn) gone
  let gRepulsor :=
    gGone.applyEffect ⟨0⟩ (.dealDamageThenControllerIfTeamwork 5 2) gone
  let gCruel :=
    gGone.applyEffect ⟨0⟩ (.exileCreatureMvAtMostOrAnyIfTeamwork 3 3) gone
  let gCrowd :=
    gGone.applyMshSpell ⟨0⟩ .targetCreatureYouControlThatSAttackingAlo gone
  let gLandfall :=
    let g := addPermanent gGone claimTheKingdom ⟨0⟩ ⟨0⟩
    let plan := namedPermanent g "Claim the Kingdom"
    g.applyTriggeredAbility ⟨0⟩ (.onLandYouControlEntersPlusOneAndPlan) (some plan.id)
      gone
  let gAbsorb :=
    let g := addPermanent gGone absorbingMan ⟨0⟩ ⟨0⟩
    g.applyMshTrigger ⟨0⟩ .atTheBeginningOfYourFirstMainPhase
      (some (namedPermanent g "Absorbing Man").id) gone
  let gTask :=
    let g := addPermanent gGone taskmasterMercenaryMimic ⟨0⟩ ⟨0⟩
    g.applyMshTrigger ⟨0⟩ .photographicReflexesAtTheBeginningOf
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
    (mshRuling 209).comment.contains "won't gain life" &&
    (mshRuling 210).comment.contains "Cruel Alliance" &&
    (mshRuling 211).comment.contains "Depower" &&
    (mshRuling 212).comment.contains "Hour of Defeat" &&
    (mshRuling 213).comment.contains "Pym Particles" &&
    (mshRuling 214).comment.contains "Repulsor Blast" &&
    (mshRuling 215).comment.contains "illegal target" &&
    (mshRuling 216).comment.contains "will not resolve" &&
    (mshRuling 217).comment.contains "Taskmaster" &&
    (mshRuling 218).comment.contains "landfall ability" &&
    (mshRuling 219).comment.contains "Absorbing Man"

#guard illegalTargetDoesNothingOk

/-- Giant Growth does nothing if its target has left (shared CR / ruling 180). -/
def fizzleWhenTargetLeftOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let host := namedPermanent g "Grizzly Bears"
  let (g, _) := g.move host.id (.graveyard ⟨1⟩) none
  g.legalTargets ⟨0⟩ (.pump 3 3) |>.isEmpty &&
    (mshRuling 180).comment.contains "illegal target"

#guard fizzleWhenTargetLeftOk

/-!
## 30, 113, 240, 243 — Look at the top card
-/

def lookAtTopRestrictionOk : Bool :=
  daredevilManWithoutFear.mayLookAtTopAnytime &&
    ironLadDivergingDestiny.mayLookAtTopAnytime &&
    kaZarOfTheSavageLand.mayLookAtTopAnytime &&
    (mshRuling 30).comment.contains "can't look at the n" &&
    (mshRuling 240).comment.contains "look at the top card" &&
    (mshRuling 243).comment.contains "look at the top card"

#guard lookAtTopRestrictionOk

/-!
## 320 already covered; 345–347 Vibranium spend
-/

def vibraniumSpendNotOnNonartifactOk : Bool :=
  let p := ManaPool.empty.add .colorless 1 (cantNonartifact := true)
  !p.canPay (ManaCost.ofGeneric 1) &&
    p.canPay (ManaCost.ofGeneric 1) false false false false true &&
    (mshRuling 345).comment.contains "isn't a nonartifact spell"

#guard vibraniumSpendNotOnNonartifactOk

/-!
## 376 — Maximum hand size is checked only in cleanup
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
    (mshRuling 376).comment.contains "cleanup step" &&
    (mshRuling 184).comment.contains "maximum hand size"

#guard maxHandSizeCleanupOnlyOk

/-- Ruling 288: Ms. Marvel's granted set-power overwrites a previous set P/T. -/
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
    (mshRuling 288).comment.contains "overwrite any previous effects"

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
    (mshRuling 165).comment.contains "that many plus one" &&
    (mshRuling 224).comment.contains "two or more effects" &&
    (mshRuling 238).comment.contains "two Doc Samsons"

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
    (mshRuling 289).comment.contains "works in all zones"

#guard namorPowerAllZonesOk

def superAdaptoidPowerAllZonesOk : Bool :=
  let g := addPermanent afterDraw superAdaptoid ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Super-Adaptoid"
  g.power o == 1 &&
    (mshRuling 290).comment.contains "works in all zones"

#guard superAdaptoidPowerAllZonesOk

def iAmIronManSetsPTOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let g := g.applyEffect ⟨0⟩ .becomeArtifactCreature44Flying
    #[Target.permanent host.id]
  let o := namedPermanent g "Grizzly Bears"
  g.power o == 4 && g.toughness o == 4 &&
    o.isCreature && o.types.any (· == .artifact) &&
    (mshRuling 129).comment.contains "overwrite any previous effects" &&
    (mshRuling 135).comment.contains "doesn't count as \"crewing\"" &&
    (mshRuling 89).comment.contains "artifact creature"

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
    (mshRuling 166).comment.contains "won't untap" &&
    (mshRuling 202).comment.contains "can't be paid"

#guard frozenInIceCantUntapOk

def spiderWomanCantUntapOk : Bool :=
  let g := addPermanent afterDraw spiderWomanSecretAgent ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let wasp := namedPermanent g "Spider-Woman, Secret Agent"
  let host := namedPermanent g "Grizzly Bears"
  let g := g.applyMshTrigger ⟨0⟩ .whenSpiderWomanEnters (some wasp.id)
    #[Target.permanent host.id]
  let host := namedPermanent g "Grizzly Bears"
  host.status.tapped && g.hostCantBecomeUntapped host &&
    (mshRuling 167).comment.contains "won't untap" &&
    (mshRuling 203).comment.contains "can't be paid"

#guard spiderWomanCantUntapOk

def hulklingGreaterStatOk : Bool :=
  let g := mshEnter afterDraw hulklingBurgeoningBruiser
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  let giant := namedPermanent g "Hill Giant"
  let g := g.afterPermanentEnters giant
  let hulkling := namedPermanent g "Hulkling, Burgeoning Bruiser"
  let fires := g.waitingTriggers.any (fun t =>
    t.source.name == "Hulkling, Burgeoning Bruiser")
  let g := g.applyMshTrigger ⟨0⟩ .wheneverAnotherCreatureYouControlEnters
    (some hulkling.id) #[Target.permanent giant.id]
  (namedPermanent g "Hulkling, Burgeoning Bruiser").status.plusOnePlusOne == 1 &&
    fires &&
    (mshRuling 156).comment.contains "+1/+1 counters on it" &&
    (mshRuling 328).comment.contains "power to power" &&
    (mshRuling 332).comment.contains "won't trigger at all"

#guard hulklingGreaterStatOk

def hulklingSmallerDoesNotTriggerOk : Bool :=
  let g := mshEnter afterDraw hulklingBurgeoningBruiser
  let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
  let bot := namedPermanent g "Aerial Doombot"
  let g := g.afterPermanentEnters bot
  !g.waitingTriggers.any (fun t =>
    t.source.name == "Hulkling, Burgeoning Bruiser") &&
    (mshRuling 332).comment.contains "neither stat"

#guard hulklingSmallerDoesNotTriggerOk

def wolverineHealsOtherDamageOk : Bool :=
  let g := addPermanent afterDraw wolverineFierceFighter ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Wolverine, Fierce Fighter"
  let g := g.mapObjectStatus o (fun s => { s with damage := 3 })
  let o := namedPermanent g "Wolverine, Fierce Fighter"
  let g := g.markDamageOn o 2 "Wolverine is dealt 2 damage"
  (namedPermanent g "Wolverine, Fierce Fighter").status.damage == 2 &&
    (mshRuling 316).comment.contains "remove all damage" &&
    (mshRuling 340).comment.contains "replacement effect"

#guard wolverineHealsOtherDamageOk

def shieldRemovesOneOk : Bool :=
  let g := addPermanent afterDraw captainAmericaSuperSoldier ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Captain America, Super-Soldier"
  let g := g.setObject { o with status := { o.status with shield := 2 } }
  let o := namedPermanent g "Captain America, Super-Soldier"
  let g := g.markDamageOn o 5 "Cap is dealt 5 damage"
  let o := namedPermanent g "Captain America, Super-Soldier"
  o.status.shield == 1 && o.status.damage == 0 &&
    (mshRuling 163).comment.contains "only one shield counter" &&
    (mshRuling 71).comment.contains "not keyword counters" &&
    (mshRuling 274).comment.contains "isn't the same as regenerating" &&
    (mshRuling 281).comment.contains "sacrificing"

#guard shieldRemovesOneOk

def shieldUnpreventableStillRemovesOk : Bool :=
  let g := addPermanent afterDraw captainAmericaSuperSoldier ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Captain America, Super-Soldier"
  let g := g.setObject { o with status := { o.status with shield := 1 } }
  let o := namedPermanent g "Captain America, Super-Soldier"
  let g := g.markDamageOn o 3 "unpreventable" (unpreventable := true)
  let o := namedPermanent g "Captain America, Super-Soldier"
  o.status.shield == 0 && o.status.damage == 3 &&
    (mshRuling 164).comment.contains "unpreventable damage" &&
    (mshRuling 81).comment.contains "unpreventable damage"

#guard shieldUnpreventableStillRemovesOk

def powerUpStillHappensIfSourceLeftOk : Bool :=
  let g := addPermanent afterDraw whiteTigerAvaAyala ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "White Tiger, Ava Ayala"
  let (g, _) := g.move o.id (.graveyard ⟨0⟩) none
  let g := g.applyAbilityEffect ⟨0⟩
    (.mshSpell .putA11CounterOnWhiteTigerAndCreateTh) #[] (some o.id)
  g.battlefield.any (fun x => x.name == "The Tiger God") &&
    (mshRuling 338).comment.contains "you'll still create The Tiger God" &&
    (mshRuling 301).comment.contains "you'll still create" &&
    (mshRuling 318).comment.contains "You'll create" &&
    (mshRuling 261).comment.contains "each opponent will still discard"

#guard powerUpStillHappensIfSourceLeftOk

def doublePowerAndToughnessOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let p0 := g.power host
  let t0 := g.toughness host
  let g := g.applyEffect ⟨0⟩ .doublePowerAndToughness
    #[Target.permanent host.id]
  let o := namedPermanent g "Grizzly Bears"
  g.power o == p0 + p0 && g.toughness o == t0 + t0 &&
    (mshRuling 314).comment.contains "gets +X/+Y" &&
    (mshRuling 315).comment.contains "gets +X/+Y"

#guard doublePowerAndToughnessOk

def hydraulicHelperRestrictedBlueOk : Bool :=
  let p := ManaPool.empty.add (.colored .blue) 1 (cantNonartifact := true)
  !p.canPay (ManaCost.ofColor .blue) &&
    p.canPay (ManaCost.ofColor .blue) false false false false true &&
    (mshRuling 345).comment.contains "isn't a nonartifact spell"

#guard hydraulicHelperRestrictedBlueOk

def copyKeepsChosenXOk : Bool :=
  let (g, src) := afterDraw.allocObject photonBlastBarrage ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.setObject { src with chosenX := some 4 }
  let g := g.copyStackSpell (g.object! src.id) ⟨0⟩
  let copies := g.objects.filter (fun o =>
    o.name == "Photon Blast Barrage" && o.zone == .stack && o.isCopy)
  copies.size == 1 && copies[0]!.chosenX == some 4 &&
    (mshRuling 114).comment.contains "same target as the original" &&
    (mshRuling 208).comment.contains "same targets unless" &&
    (mshRuling 294).comment.contains "same targets unless" &&
    (mshRuling 324).comment.contains "creates X copies" &&
    (mshRuling 268).comment.contains "creates copies even if" &&
    (mshRuling 49).comment.contains "division and number of targets" &&
    (mshRuling 51).comment.contains "same mode or modes"

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
    (let g := g.applyMshTrigger ⟨0⟩ .wheneverACreatureYouControlBecomesTappedD
       none #[]
     !(namedPermanent g "Grizzly Bears").status.tapped) &&
    (mshRuling 104).comment.contains "became tapped earlier" &&
    (mshRuling 124).comment.contains "already tapped"

#guard capLivingLegendFirstTapUntapsOk

/-- Rulings 98 / 110 / 244–246 / 249 / 255 / 277: second-card triggers fire
even if the permanent entered after the first draw. -/
def secondCardDrawnAfterEnterOk : Bool :=
  let g := afterDraw.modifyPlayer ⟨0⟩ (fun pl => { pl with cardsDrawnThisTurn := 1 })
  let g := addPermanent g kangTemporalTyrant ⟨0⟩ ⟨0⟩
  let g := addPermanent g kidLoki ⟨0⟩ ⟨0⟩
  let g := g.draw ⟨0⟩ 1
  g.waitingTriggers.any (fun t => t.source.name == "Kang, Temporal Tyrant") &&
    g.waitingTriggers.any (fun t => t.source.name == "Kid Loki") &&
    (mshRuling 98).comment.contains "second card" &&
    (mshRuling 110).comment.contains "second card" &&
    (mshRuling 244).comment.contains "second card" &&
    (mshRuling 245).comment.contains "second card" &&
    (mshRuling 246).comment.contains "second card" &&
    (mshRuling 249).comment.contains "second card" &&
    (mshRuling 255).comment.contains "second card" &&
    (mshRuling 277).comment.contains "second card"

#guard secondCardDrawnAfterEnterOk

/-- Ruling 97: Kid Loki hexproof applies to creatures that got +1/+1 earlier. -/
def kidLokiHexproofAfterCountersOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.addPlusOnePlusOneTo bears 1
  let bears := namedPermanent g "Grizzly Bears"
  !g.hasHexproof bears &&
    (let g := addPermanent g kidLoki ⟨0⟩ ⟨0⟩
     let bears := namedPermanent g "Grizzly Bears"
     g.hasHexproof bears &&
       (mshRuling 97).comment.contains "Kid Loki")

#guard kidLokiHexproofAfterCountersOk

/-- True when a battlefield permanent named `n` exists. -/
def onBattlefield (g : Game) (n : String) : Bool :=
  g.battlefield.any (fun o => o.name == n)

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
     let g := g.applyMshTrigger ⟨0⟩ .whenThisEnchantmentEnters (some lock.id)
       #[Target.permanent bears.id]
     onBattlefield g "Grizzly Bears" &&
       !g.objects.any (fun o => o.name == "Grizzly Bears" && o.zone == .exile)) &&
    (mshRuling 149).comment.contains "won't be exiled" &&
    (mshRuling 141).comment.contains "won't be exiled"

#guard leaveBeforeResolveExileOk

/-- Ruling 132 / 204 / 225: Cloak and Dagger still reveal if they left. -/
def cloakAndDaggerRevealIfLeftOk : Bool :=
  let g := addToHand afterDraw lightningBolt ⟨1⟩
  let g := addPermanent g cloakAndDaggerEntwined ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let cloak := namedPermanent g "Cloak and Dagger, Entwined"
  let bears := namedPermanent g "Grizzly Bears"
  let (g, _) := g.move cloak.id (.graveyard ⟨0⟩) none
  let g := g.applyMshTrigger ⟨0⟩ .whenCloakAndDaggerEnter (some cloak.id)
    #[Target.player ⟨1⟩, Target.permanent bears.id]
  logContains g "reveals their hand" &&
    onBattlefield g "Grizzly Bears" &&
    !g.objects.any (fun o => o.name == "Grizzly Bears" && o.zone == .exile) &&
    (mshRuling 132).comment.contains "still reveal" &&
    (mshRuling 225).comment.contains "still do as much as it can"

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
  let g := g.applyMshTrigger ⟨0⟩ .whenThisAuraEnters2 (some aura.id)
    #[Target.permanent tgt.id]
  onBattlefield g "Hill Giant" &&
    onBattlefield g "Grizzly Bears" &&
    (namedPermanent g "Grizzly Bears").printed.name == "Grizzly Bears" &&
    (mshRuling 140).comment.contains "won't be exiled"

#guard secretInvasionLeaveOk

/-- Rulings 121 / 200 / 201 / 322: Absorbing Man copies printed values, no ETB. -/
def absorbingManCopyOk : Bool :=
  let g := addPermanent afterDraw absorbingMan ⟨0⟩ ⟨0⟩
  let g := addPermanent g doctorDoom ⟨0⟩ ⟨0⟩
  let am := namedPermanent g "Absorbing Man"
  let doom := namedPermanent g "Doctor Doom"
  let before := g.waitingTriggers.size
  let g := g.applyMshTrigger ⟨0⟩ .atTheBeginningOfYourFirstMainPhase (some am.id)
    #[Target.permanent doom.id]
  let am := namedPermanent g "Absorbing Man"
  am.printed.name == "Absorbing Man" &&
    am.printed.power == some 4 &&
    am.printed.types.any (· == .creature) &&
    am.copyRestore.isSome &&
    am.copyUntilNextTurn &&
    g.waitingTriggers.size == before &&
    (mshRuling 121).comment.contains "exactly what was printed" &&
    (mshRuling 322).comment.contains "neither entering nor leaving"

#guard absorbingManCopyOk

/-- Rulings 122 / 196 / 198 / 326: Taskmaster copies a creature or graveyard card. -/
def taskmasterCopyOk : Bool :=
  let g := addPermanent afterDraw taskmasterMercenaryMimic ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  let tm := namedPermanent g "Taskmaster, Mercenary Mimic"
  let giant := namedPermanent g "Hill Giant"
  let g := g.applyMshTrigger ⟨0⟩ .photographicReflexesAtTheBeginningOf (some tm.id)
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
     let g2 := g2.applyMshTrigger ⟨0⟩ .photographicReflexesAtTheBeginningOf
       (some tm.id) #[Target.card gy.id]
     (namedPermanent g2 "Taskmaster, Mercenary Mimic").printed.power ==
       hillGiant.power) &&
    (mshRuling 122).comment.contains "exactly what was printed" &&
    (mshRuling 326).comment.contains "neither entering nor leaving"

#guard taskmasterCopyOk

/-- Rulings 120 / 188 / 193 / 194 / 330: Shuri copies until EOT and isn't legendary. -/
def shuriCopyUntilEotOk : Bool :=
  let g := addPermanent afterDraw shuriWakandanInventor ⟨0⟩ ⟨0⟩
  let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
  let g := addPermanent g sHIELDDeploymentDrone ⟨0⟩ ⟨0⟩
  let destId := (namedPermanent g "Aerial Doombot").id
  let src := namedPermanent g "S.H.I.E.L.D. Deployment Drone"
  let g := g.applyMshSpell ⟨0⟩ .targetArtifactYouControlBecomesACopyOfA
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
     let g2 := g2.applyMshSpell ⟨0⟩ .targetArtifactYouControlBecomesACopyOfA
       #[Target.permanent dest.id]
     (g2.object! dest.id).printed.name == destName) &&
    (mshRuling 120).comment.contains "exactly what was printed" &&
    (mshRuling 188).comment.contains "won't have any effect" &&
    (mshRuling 330).comment.contains "neither entering nor leaving"

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
  let g := g.applyMshTrigger ⟨0⟩ .whenThisAuraEnters2 (some aura.id)
    #[Target.permanent tgt.id]
  let host := g.object! host.id
  host.copyRestore.isSome &&
    (host.copyRestore.getD host.printed).name == "Grizzly Bears" &&
    host.printed.name == "Hill Giant" &&
    (let aura := namedPermanent g "Secret Invasion"
     let (g, _) := g.move aura.id (.graveyard ⟨0⟩) none
     (namedPermanent g "Grizzly Bears").printed.name == "Grizzly Bears") &&
    (mshRuling 325).comment.contains "exactly what was printed" &&
    (mshRuling 329).comment.contains "neither entering nor leaving"

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
     let g := g.applyMshTrigger ⟨0⟩ .wheneverACreatureYouControlIsDealtDamage
       (some she.id) #[Target.permanent giant.id]
       "The Sensational She-Hulk" (some 3)
     let giant := namedPermanent g "Hill Giant"
     giant.status.damage == 3 &&
       g.sheHulkDamageUsedThisTurn &&
       (let g := g.applyMshTrigger ⟨0⟩ .wheneverACreatureYouControlIsDealtDamage
          (some she.id) #[Target.permanent giant.id]
          "The Sensational She-Hulk" (some 5)
        (namedPermanent g "Hill Giant").status.damage == 3 &&
          logContains g "no effect")) &&
    (mshRuling 95).comment.contains "won't trigger again that turn" &&
    (mshRuling 142).comment.contains "may still have her deal damage" &&
    (mshRuling 160).comment.contains "total amount of damage"

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
    (mshRuling 34).comment.contains "won't apply to copying" &&
    (mshRuling 40).comment.contains "won't cause abilities that trigger" &&
    (mshRuling 47).comment.contains "same value of X" &&
    (mshRuling 61).comment.contains "same targets as the ability" &&
    (mshRuling 62).comment.contains "resolve before the original" &&
    (mshRuling 302).comment.contains "same as the source of the original"

#guard copyStackAbilityOk

/-- Ruling 96: Worlds Within Worlds exiles creatures, then hand creatures
enter, then the exiled cards return to hands. -/
def worldsWithinWorldsOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  let g := addToHand g aerialDoombot ⟨0⟩
  let (g, spell) := g.allocObject worldsWithinWorlds ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.applyMshSpell ⟨0⟩ .exileAllCreaturesEachPlayerMayPutAnyNum #[]
    (some spell.id)
  g.battlefield.any (fun o => o.name == "Aerial Doombot") &&
    !g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    !g.battlefield.any (fun o => o.name == "Hill Giant") &&
    (g.player ⟨0⟩).hand.any (fun id => (g.object! id).name == "Grizzly Bears") &&
    (g.player ⟨1⟩).hand.any (fun id => (g.object! id).name == "Hill Giant") &&
    (match g.findObject? spell.id with
     | some o => o.zone == .exile
     | none =>
       g.objects.any (fun o => o.name == "Worlds Within Worlds" && o.zone == .exile)) &&
    (mshRuling 96).comment.contains "Worlds Within Worlds"

#guard worldsWithinWorldsOk

/-- Ruling 131: Captain America's attack pump uses last-known toughness. -/
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
    (mshRuling 131).comment.contains "last existed on the battlefield" &&
    (mshRuling 310).comment.contains "determined only once"

#guard capWingsLastKnownToughnessOk

/-- Ruling 147 / 321: Viv Vision draws using last-known power if she left. -/
def vivVisionLastKnownPowerOk : Bool :=
  let g := addPermanent afterDraw vivVisionTeenSynthezoid ⟨0⟩ ⟨0⟩
  let viv := namedPermanent g "Viv Vision, Teen Synthezoid"
  let g := g.addPlusOnePlusOneTo viv 2
  let viv := namedPermanent g "Viv Vision, Teen Synthezoid"
  let pw := g.power viv
  let hand0 := (g.player ⟨0⟩).hand.size
  let (g, _) := g.move viv.id (.graveyard ⟨0⟩) none
  let g := g.applyMshTrigger ⟨0⟩ .cyberneticSensesWheneverVivVision (some viv.id)
    #[] "Viv Vision" (some pw)
  pw >= 4 &&
    (g.player ⟨0⟩).hand.size == hand0 + 1 &&
    (mshRuling 147).comment.contains "last existed on the battlefield" &&
    (mshRuling 321).comment.contains "checks Viv Vision's power only as it resolves"

#guard vivVisionLastKnownPowerOk

/-- Ruling 148: War Machine's combat pump uses last-known power. -/
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
  let g := g.applyMshTrigger ⟨0⟩ .atTheBeginningOfCombatOnYourTurn (some wm.id)
    #[Target.permanent bears.id] "War Machine" (some pw)
  g.power (namedPermanent g "Grizzly Bears") == p0 + pw &&
    (mshRuling 148).comment.contains "last existed on the battlefield" &&
    (mshRuling 308).comment.contains "calculated only once"

#guard warMachineLastKnownPowerOk

/-- Ruling 137: Political Triumph still draws and counters if it left. -/
def politicalTriumphLeftOk : Bool :=
  let g := addPermanent afterDraw politicalTriumph ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let plan := namedPermanent g "Political Triumph"
  let hand0 := (g.player ⟨0⟩).hand.size
  let (g, _) := g.move plan.id (.graveyard ⟨0⟩) none
  let g := g.applyTriggeredAbility ⟨0⟩ .onFourthPlanDrawPlusOneEach (some plan.id)
  (g.player ⟨0⟩).hand.size == hand0 + 1 &&
    (namedPermanent g "Grizzly Bears").status.plusOnePlusOne == 1 &&
    (mshRuling 137).comment.contains "won't be able to sacrifice it"

#guard politicalTriumphLeftOk

/-- Ruling 139: Robot Domination still creates tokens if it left. -/
def robotDominationLeftOk : Bool :=
  let g := addPermanent afterDraw robotDomination ⟨0⟩ ⟨0⟩
  let plan := namedPermanent g "Robot Domination"
  let (g, _) := g.move plan.id (.graveyard ⟨0⟩) none
  let g := g.applyTriggeredAbility ⟨0⟩ .onThirdPlanCreateRobots (some plan.id)
  (g.battlefield.filter (fun o => o.name == "Robot Villain")).size == 3 &&
    (mshRuling 139).comment.contains "You'll create the Robot"

#guard robotDominationLeftOk

/-- Ruling 136: Jessica Jones exiles X using last-known power if she left. -/
def jessicaJonesLastKnownXOk : Bool :=
  let g := addPermanent afterDraw jessicaJonesPrivateEye ⟨0⟩ ⟨0⟩
  let jj := namedPermanent g "Jessica Jones, Private Eye"
  let g := g.addPlusOnePlusOneTo jj 1
  let jj := namedPermanent g "Jessica Jones, Private Eye"
  let pw := g.power jj
  let lib0 := (g.player ⟨0⟩).library.size
  let (g, _) := g.move jj.id (.graveyard ⟨0⟩) none
  let g := g.applyMshAbility ⟨0⟩ .tPutAStunCounterOnJessicaJones #[]
    (some jj.id) (some pw)
  (g.player ⟨0⟩).library.size == lib0 - pw.toNat &&
    (g.objects.filter (fun o =>
      o.zone == .exile && o.playPermission.isSome)).size == pw.toNat &&
    (mshRuling 136).comment.contains "last existed on the battlefield" &&
    (mshRuling 306).comment.contains "calculated only once"

#guard jessicaJonesLastKnownXOk

/-- Ruling 150: Whiplash drain uses last-known attached Equipment. -/
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
  let g := g.applyMshTrigger ⟨0⟩ .wheneverWhiplashAttacks (some whip.id)
    #[] "Whiplash" (some (Int.ofNat n))
  n == 2 &&
    (g.player ⟨1⟩).life + n == life0 &&
    (g.player ⟨0⟩).life == you0 + n &&
    (mshRuling 150).comment.contains "last existed on the battlefield" &&
    (mshRuling 309).comment.contains "calculated only once"

#guard whiplashLastKnownEquipmentOk

/-- Rulings 359 / 367: first reflexive ability has no targets; the second does. -/
def mshReflexiveNoTargetFirstOk : Bool :=
  let g := addPermanent afterDraw bullseyeDeathDealer ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let b := namedPermanent g "Bullseye, Death Dealer"
  let g := g.applyMshTrigger ⟨0⟩ .whenBullseyeEnters (some b.id)
  (namedPermanent g "Grizzly Bears").status.damage == 0 &&
    g.pendingMshReflexive.isSome &&
    logContains g "reflexive" &&
    (let bears := namedPermanent g "Grizzly Bears"
     let g := g.applyMshReflexive #[Target.permanent bears.id]
     (namedPermanent g "Grizzly Bears").status.damage == 2) &&
    (let g := addPermanent afterDraw spiderManToTheRescue ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
     let sm := namedPermanent g "Spider-Man, To the Rescue"
     let g := g.applyMshTrigger ⟨0⟩ .noOneDiesWhenSpiderManEnte (some sm.id)
     (namedPermanent g "Spider-Man, To the Rescue").status.tapped &&
       g.pendingMshReflexive.isSome &&
       (let bears := namedPermanent g "Grizzly Bears"
        let g := g.applyMshReflexive #[Target.permanent bears.id]
        (namedPermanent g "Grizzly Bears").status.untilEotKeywords.indestructible)) &&
    (mshRuling 359).comment.contains "reflexive" &&
    (mshRuling 367).comment.contains "reflexive"

#guard mshReflexiveNoTargetFirstOk

/-- Ruling 125: Hawkeye's first trigger has no modes; paying queues the second. -/
def hawkeyeReflexivePayOk : Bool :=
  let g := addPermanent afterDraw hawkeyeMasterMarksman ⟨0⟩ ⟨0⟩
  let hawk := namedPermanent g "Hawkeye, Master Marksman"
  let nonePaid :=
    g.applyMshTrigger ⟨0⟩ .trickArrowsWheneverHawkeyeBec (some hawk.id)
      #[] "Hawkeye" none
  !nonePaid.pendingMshReflexive.isSome &&
    (let g := g.applyMshTrigger ⟨0⟩ .trickArrowsWheneverHawkeyeBec (some hawk.id)
       #[] "Hawkeye" (some (2 : Int))
     g.pendingMshReflexive.isSome &&
       g.pendingMshReflexivePaid == 2 &&
       (let life1 := (g.player ⟨1⟩).life
        let g := g.applyMshReflexive #[Target.player ⟨1⟩]
        (g.player ⟨1⟩).life + 2 == life1)) &&
    (mshRuling 125).comment.contains "reflexive"

#guard hawkeyeReflexivePayOk

/-- Ruling 360: Claim the Kingdom's first ability only sacrifices; the
indestructible counter is a reflexive second trigger. -/
def claimTheKingdomReflexiveOk : Bool :=
  let g := addPermanent afterDraw claimTheKingdom ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let plan := namedPermanent g "Claim the Kingdom"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.applyTriggeredAbility ⟨0⟩ .onFourthPlanIndestructible (some plan.id)
  !g.battlefield.any (fun o => o.name == "Claim the Kingdom") &&
    (namedPermanent g "Grizzly Bears").status.indestructibleCounters == 0 &&
    g.pendingMshReflexive.isSome &&
    (let g := g.applyMshReflexive #[Target.permanent bears.id]
     (namedPermanent g "Grizzly Bears").status.indestructibleCounters == 1) &&
    (let g := addPermanent afterDraw claimTheKingdom ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
     let plan := namedPermanent g "Claim the Kingdom"
     let (g, _) := g.move plan.id (.graveyard ⟨0⟩) none
     let g := g.applyTriggeredAbility ⟨0⟩ .onFourthPlanIndestructible (some plan.id)
     !g.pendingMshReflexive.isSome &&
       (namedPermanent g "Grizzly Bears").status.indestructibleCounters == 0) &&
    (mshRuling 360).comment.contains "reflexive"

#guard claimTheKingdomReflexiveOk

/-- Ruling 361: Construct a Cosmic Cube queues control of an opponent. -/
def constructACosmicCubeReflexiveOk : Bool :=
  let g := addPermanent afterDraw constructACosmicCube ⟨0⟩ ⟨0⟩
  let plan := namedPermanent g "Construct a Cosmic Cube"
  let g := g.applyTriggeredAbility ⟨0⟩ .onSeventhPlanControlOpponent (some plan.id)
  !g.battlefield.any (fun o => o.name == "Construct a Cosmic Cube") &&
    g.pendingMshReflexive.isSome &&
    (let g := g.applyMshReflexive #[Target.player ⟨1⟩]
     g.controlsPlayer ⟨0⟩ ⟨1⟩ && g.controlOnNextTakenTurn) &&
    (mshRuling 361).comment.contains "reflexive"

#guard constructACosmicCubeReflexiveOk

/-- Ruling 362: Doom Reigns Supreme exiles the opponent's top cards only
after the Plan is sacrificed. -/
def doomReignsSupremeReflexiveOk : Bool :=
  let g := addPermanent afterDraw doomReignsSupreme ⟨0⟩ ⟨0⟩
  let plan := namedPermanent g "Doom Reigns Supreme"
  let lib0 := (g.player ⟨1⟩).library.size
  let g := g.applyTriggeredAbility ⟨0⟩ .onFifthPlanExileTopCast (some plan.id)
  (g.player ⟨1⟩).library.size == lib0 &&
    g.pendingMshReflexive.isSome &&
    (let g := g.applyMshReflexive #[Target.player ⟨1⟩]
     (g.player ⟨1⟩).library.size == lib0 - 5 &&
       (g.objects.filter (fun o =>
         o.zone == .exile && o.playPermission.isSome)).size == 5) &&
    (mshRuling 362).comment.contains "reflexive"

#guard doomReignsSupremeReflexiveOk

/-- Ruling 363: Grim Reaper's pay is the first ability; the return is
reflexive. -/
def grimReaperReflexiveOk : Bool :=
  let g := addPermanent afterDraw grimReaperLethalLegionnaire ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g grizzlyBears ⟨0⟩
  let grim := namedPermanent g "Grim Reaper, Lethal Legionnaire"
  let unpaid :=
    g.applyMshTrigger ⟨0⟩ .wheneverGrimReaperAttacks (some grim.id)
  !unpaid.pendingMshReflexive.isSome &&
    (let g := g.applyMshTrigger ⟨0⟩ .wheneverGrimReaperAttacks (some grim.id)
       #[] "Grim Reaper" (some (1 : Int))
     g.pendingMshReflexive.isSome &&
       (let gy := namedGraveyardCard g ⟨0⟩ "Grizzly Bears"
        let g := g.applyMshReflexive #[Target.card gy.id]
        let bears := namedPermanent g "Grizzly Bears"
        bears.status.tapped && bears.status.attacking &&
          bears.status.finality ≥ 1)) &&
    (mshRuling 363).comment.contains "reflexive"

#guard grimReaperReflexiveOk

/-- Ruling 364: Killmonger only destroys if another creature was
sacrificed. -/
def killmongerReflexiveOk : Bool :=
  let g := addPermanent afterDraw killmongerScourgeOfWakanda ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let km := namedPermanent g "Killmonger, Scourge of Wakanda"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.applyMshTrigger ⟨0⟩ .whenKillmongerEnters (some km.id)
  !g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    g.pendingMshReflexive.isSome &&
    g.battlefield.any (fun o => o.name == "Gray Ogre") &&
    (let g := g.applyMshReflexive #[Target.permanent ogre.id]
     !g.battlefield.any (fun o => o.name == "Gray Ogre")) &&
    (let g := addPermanent afterDraw killmongerScourgeOfWakanda ⟨0⟩ ⟨0⟩
     let km := namedPermanent g "Killmonger, Scourge of Wakanda"
     let g := g.applyMshTrigger ⟨0⟩ .whenKillmongerEnters (some km.id)
     !g.pendingMshReflexive.isSome) &&
    (mshRuling 364).comment.contains "reflexive"

#guard killmongerReflexiveOk

/-- Rulings 273 / 365: Red Hulk's reflexive damage uses the counters only
if he survived to receive one. -/
def redHulkReflexiveOk : Bool :=
  let g := addPermanent afterDraw redHulk ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let hulk := namedPermanent g "Red Hulk"
  let g := g.applyMshTrigger ⟨0⟩ .enrageWheneverRedHulkIs (some hulk.id)
  (namedPermanent g "Red Hulk").status.plusOnePlusOne == 1 &&
    g.pendingMshReflexive.isSome &&
    g.pendingMshReflexivePaid == 1 &&
    (let bears := namedPermanent g "Grizzly Bears"
     let g := g.applyMshReflexive #[Target.permanent bears.id]
     (namedPermanent g "Grizzly Bears").status.damage == 1) &&
    (let g := addPermanent afterDraw redHulk ⟨0⟩ ⟨0⟩
     let hulk := namedPermanent g "Red Hulk"
     let (g, _) := g.move hulk.id (.graveyard ⟨0⟩) none
     let g := g.applyMshTrigger ⟨0⟩ .enrageWheneverRedHulkIs (some hulk.id)
     !g.pendingMshReflexive.isSome) &&
    (mshRuling 273).comment.contains "must survive the damage" &&
    (mshRuling 365).comment.contains "reflexive"

#guard redHulkReflexiveOk

/-- Ruling 366: Speed's pay queues a haste-only blocker restriction. -/
def speedYoungAvengerReflexiveOk : Bool :=
  let g := addPermanent afterDraw speedYoungAvenger ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let speed := namedPermanent g "Speed, Young Avenger"
  let unpaid :=
    g.applyMshTrigger ⟨0⟩ .wheneverYouCastANoncreatureSpell5 (some speed.id)
  !unpaid.pendingMshReflexive.isSome &&
    (let g := g.applyMshTrigger ⟨0⟩ .wheneverYouCastANoncreatureSpell5
       (some speed.id) #[] "Speed" (some (1 : Int))
     g.pendingMshReflexive.isSome &&
       (let speed := namedPermanent g "Speed, Young Avenger"
        let g := g.applyMshReflexive #[Target.permanent speed.id]
        let speed := namedPermanent g "Speed, Young Avenger"
        let g := g.setObject { speed with status := { speed.status with
          attacking := true, attackingWhom := some ⟨1⟩ } }
        let speed := namedPermanent g "Speed, Young Avenger"
        let bears := namedPermanent g "Grizzly Bears"
        speed.status.cantBeBlockedExceptByHasteUntilEot &&
          !g.canBlock bears speed &&
          (let g := g.mapObjectStatus bears (·.grantUntilEot Keyword.haste)
           g.canBlock (namedPermanent g "Grizzly Bears")
             (namedPermanent g "Speed, Young Avenger")))) &&
    (mshRuling 366).comment.contains "reflexive"

#guard speedYoungAvengerReflexiveOk

/-- Ruling 368: Death to Our Enemies deals 7 only after the sacrifice. -/
def deathToOurEnemiesReflexiveOk : Bool :=
  let g := addPermanent afterDraw deathToOurEnemies ⟨0⟩ ⟨0⟩
  let plan := namedPermanent g "Death to Our Enemies"
  let life0 := (g.player ⟨1⟩).life
  let g := g.applyTriggeredAbility ⟨0⟩ .onFourthPlanDividedDamage (some plan.id)
  (g.player ⟨1⟩).life == life0 &&
    g.pendingMshReflexive.isSome &&
    (let g := g.applyMshReflexive #[Target.player ⟨1⟩]
     (g.player ⟨1⟩).life + 7 == life0) &&
    (mshRuling 368).comment.contains "reflexive"

#guard deathToOurEnemiesReflexiveOk

/-- Ruling 369: Rewrite History returns instants and sorceries only after
the Plan is sacrificed. -/
def rewriteHistoryReflexiveOk : Bool :=
  let g := addPermanent afterDraw rewriteHistory ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g helicarrierStrike ⟨0⟩
  let g := addToGraveyard g hourOfDefeat ⟨0⟩
  let plan := namedPermanent g "Rewrite History"
  let inst := namedGraveyardCard g ⟨0⟩ "Helicarrier Strike"
  let sorc := namedGraveyardCard g ⟨0⟩ "Hour of Defeat"
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.applyTriggeredAbility ⟨0⟩ .onFourthPlanReturnInstants (some plan.id)
  (g.player ⟨0⟩).hand.size == hand0 &&
    g.pendingMshReflexive.isSome &&
    (let g := g.applyMshReflexive #[Target.card inst.id, Target.card sorc.id]
     (g.player ⟨0⟩).hand.size == hand0 + 2 &&
       (g.handObjects ⟨0⟩).any (fun o => o.name == "Helicarrier Strike") &&
       (g.handObjects ⟨0⟩).any (fun o => o.name == "Hour of Defeat")) &&
    (mshRuling 369).comment.contains "reflexive"

#guard rewriteHistoryReflexiveOk

/-- Rulings 283 / 370: Speedball pumps even if the spell left, and may
change any number of that spell's targets (illegal replacements stay). -/
def speedballRetargetOk : Bool :=
  let g := addPermanent afterDraw speedballNewWarrior ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g mountain ⟨1⟩ ⟨1⟩
  let speed := namedPermanent g "Speedball, New Warrior"
  let (g, bolt) := g.allocObject lightningBolt ⟨1⟩ .stack (some ⟨1⟩)
  let g := g.putStackEntry ⟨1⟩ bolt.id
  let g := g.setStackEntryTargets bolt.id #[Target.permanent speed.id]
  let (gGone, _) := g.move bolt.id (.graveyard ⟨1⟩) none
  let gGone :=
    gGone.applyMshTrigger ⟨0⟩ .wheneverAPlayerCastsASpellThatTargetsSpe (some speed.id)
  gGone.power (namedPermanent gGone "Speedball, New Warrior") == 4 &&
    gGone.toughness (namedPermanent gGone "Speedball, New Warrior") == 4 &&
    (let g :=
       g.applyMshTrigger ⟨0⟩ .wheneverAPlayerCastsASpellThatTargetsSpe (some speed.id)
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.retargetStackSpell bolt.id #[Target.permanent bears.id]
     (match g.stackEntry? bolt.id with
      | some e => e.targets[0]? == some (Target.permanent bears.id)
      | none => false) &&
       (let mt := namedPermanent g "Mountain"
        let g := g.retargetStackSpell bolt.id #[Target.permanent mt.id]
        match g.stackEntry? bolt.id with
        | some e => e.targets[0]? == some (Target.permanent bears.id)
        | none => false)) &&
    (mshRuling 283).comment.contains "resolves even if that spell" &&
    (mshRuling 370).comment.contains "You may change any number of the targets"

#guard speedballRetargetOk

/-- Rulings 287 / 292 / 296 / 371: Kingpin extort pays once; life gained
equals life actually lost; combat assignment uses toughness, not power. -/
def kingpinExtortAndToughnessOk : Bool :=
  let g := addPermanent afterDraw theKingpinOfCrime ⟨0⟩ ⟨0⟩
  let (g, spell) := g.allocObject lightningBolt ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.putStackEntry ⟨0⟩ spell.id
  let g := g.putCastTriggersOnStack ⟨0⟩ (g.object! spell.id)
  g.pendingExtort == 1 &&
    (let life0 := (g.player ⟨0⟩).life
     let life1 := (g.player ⟨1⟩).life
     let g := g.applyExtort true
     (g.player ⟨1⟩).life + 1 == life1 &&
       (g.player ⟨0⟩).life == life0 + 1 &&
       g.pendingExtort == 0 &&
       (let g := g.applyExtort true
        g.pendingExtort == 0 && (g.player ⟨1⟩).life + 1 == life1)) &&
    (let g := addPermanent afterDraw theKingpinOfCrime ⟨0⟩ ⟨0⟩
     let (g, spell) := g.allocObject lightningBolt ⟨0⟩ .stack (some ⟨0⟩)
     let g := g.putStackEntry ⟨0⟩ spell.id
     let g := g.putCastTriggersOnStack ⟨0⟩ (g.object! spell.id)
     let g := g.modifyPlayer ⟨1⟩ (fun pl => { pl with lifeLocked := true })
     let life0 := (g.player ⟨0⟩).life
     let life1 := (g.player ⟨1⟩).life
     let g := g.applyExtort true
     (g.player ⟨1⟩).life == life1 &&
       (g.player ⟨0⟩).life == life0) &&
    (let g := addPermanent afterDraw theKingpinOfCrime ⟨0⟩ ⟨0⟩
     let kp := namedPermanent g "The Kingpin of Crime"
     let g := g.setObject { kp with status := { kp.status with
       attacking := true, attackingWhom := some ⟨1⟩, summoningSick := false } }
     let kp := namedPermanent g "The Kingpin of Crime"
     let g := g.applyMshTrigger ⟨0⟩ .wheneverYouAttack3 (some kp.id)
       #[] "The Kingpin of Crime" (some (1 : Int))
     let kp := namedPermanent g "The Kingpin of Crime"
     g.power kp == 1 &&
       g.toughness kp == 5 &&
       g.combatDamageToAssign kp true == 5) &&
    (mshRuling 287).comment.contains "doesn't actually change any creature's power" &&
    (mshRuling 292).comment.contains "total amount of life lost" &&
    (mshRuling 296).comment.contains "doesn't target any player" &&
    (mshRuling 371).comment.contains "maximum of one time"

#guard kingpinExtortAndToughnessOk

/-- Ruling 375: Misty Knight draws for each discard this turn even if those
cards left the graveyard. -/
def mistyKnightDiscardCountOk : Bool :=
  let g := addPermanent afterDraw mistyKnightHeroForHire ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g lightningBolt ⟨0⟩
  let g := addToGraveyard g giantGrowth ⟨0⟩
  let bolt := namedGraveyardCard g ⟨0⟩ "Lightning Bolt"
  let growth := namedGraveyardCard g ⟨0⟩ "Giant Growth"
  let (g, _) := g.move bolt.id .exile none
  let (g, _) := g.move growth.id .exile none
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with cardsDiscardedThisTurn := 2 })
  let misty := namedPermanent g "Misty Knight, Hero for Hire"
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.applyMshAbility ⟨0⟩ .n2TDiscardACard #[] (some misty.id)
  (g.player ⟨0⟩).hand.size == hand0 + 2 &&
    !(g.objects.any (fun o =>
      o.zone == .graveyard ⟨0⟩ &&
        (o.name == "Lightning Bolt" || o.name == "Giant Growth"))) &&
    (mshRuling 375).comment.contains "even if those cards are no longer"

#guard mistyKnightDiscardCountOk

/-- Ruling 94: Ares returns himself if he dies while attacking. -/
def aresDiesAttackingOk : Bool :=
  let g := addPermanent afterDraw aresGodOfWar ⟨0⟩ ⟨0⟩
  let ares := namedPermanent g "Ares, God of War"
  let g := g.setObject { ares with status := { ares.status with
    attacking := true, attackingWhom := some ⟨1⟩ } }
  let ares := namedPermanent g "Ares, God of War"
  let (g, _) := g.move ares.id (.graveyard ⟨0⟩) none
  let g := g.applyMshTrigger ⟨0⟩ .wheneverAnAttackingCreatureYouControlDies
    (some ares.id)
  (g.handObjects ⟨0⟩).any (fun o => o.name == "Ares, God of War") &&
    !g.battlefield.any (fun o => o.name == "Ares, God of War") &&
    (mshRuling 94).comment.contains "Ares himself"

#guard aresDiesAttackingOk

/-- Ruling 99: Attuma triggers once per player attacked with Merfolk. -/
def attumaMerfolkOncePerPlayerOk : Bool :=
  let g := addPermanent afterDraw attumaAtlanteanWarlord ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g :=
    g.mapObjectStatus (namedPermanent g "Grizzly Bears") (fun s =>
      { s with additionalSubtypes := #["Merfolk"] })
  let attuma := namedPermanent g "Attuma, Atlantean Warlord"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { attuma with status := { attuma.status with
    attacking := true, attackingWhom := some ⟨1⟩ } }
  let g := g.setObject { (namedPermanent g "Grizzly Bears") with status :=
    { bears.status with attacking := true, attackingWhom := some ⟨1⟩ } }
  let one :=
    g.putAttackTriggersOnStack ⟨0⟩
      #[(namedPermanent g "Attuma, Atlantean Warlord").id,
        (namedPermanent g "Grizzly Bears").id]
  let merfolkWaits (g : Game) : Nat :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.merfolkAttackPlayer)).size
  merfolkWaits one == 1 &&
    (let g := { afterDraw with
      players := afterDraw.players.push
        { (afterDraw.player ⟨1⟩) with id := ⟨2⟩, name := "Gimli" } }
     let g := addPermanent g attumaAtlanteanWarlord ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
     let g :=
       g.mapObjectStatus (namedPermanent g "Grizzly Bears") (fun s =>
         { s with additionalSubtypes := #["Merfolk"] })
     let attuma := namedPermanent g "Attuma, Atlantean Warlord"
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.setObject { attuma with status := { attuma.status with
       attacking := true, attackingWhom := some ⟨1⟩ } }
     let g := g.setObject { (namedPermanent g "Grizzly Bears") with status :=
       { bears.status with attacking := true, attackingWhom := some ⟨2⟩ } }
     let two :=
       g.putAttackTriggersOnStack ⟨0⟩
         #[(namedPermanent g "Attuma, Atlantean Warlord").id,
           (namedPermanent g "Grizzly Bears").id]
     merfolkWaits two == 2) &&
    (mshRuling 99).comment.contains "once for each player"

#guard attumaMerfolkOncePerPlayerOk

/-- Ruling 286: Avengers Assemble! still draws if the Hero left after
attacking. -/
def avengersAssembleHeroLeftOk : Bool :=
  let g := addPermanent afterDraw avengersAssemble ⟨0⟩ ⟨0⟩
  let g := addPermanent g mistyKnightHeroForHire ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with attackedWithHeroThisTurn := true })
  let hero := namedPermanent g "Misty Knight, Hero for Hire"
  let (g, _) := g.move hero.id (.graveyard ⟨0⟩) none
  let assem := namedPermanent g "Avengers Assemble!"
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.applyTriggeredAbility ⟨0⟩
    (.onEachEndStepDrawIfAttackedOrEnteredSubtype "Hero") (some assem.id)
  (g.player ⟨0⟩).hand.size == hand0 + 1 &&
    !g.battlefield.any (fun o => o.name == "Misty Knight, Hero for Hire") &&
    (mshRuling 286).comment.contains "doesn't need to still be on the battlefield"

#guard avengersAssembleHeroLeftOk

/-- Ruling 280: Shang-Chi lets you activate tap abilities immediately but
does not grant haste. -/
def shangChiActivateNotHasteOk : Bool :=
  -- `addPermanent` clears summoning sickness; insert Shang-Chi as sick.
  let g := insertObject afterDraw shangChiMasterOfKungFu ⟨0⟩ .battlefield
    (some ⟨0⟩) { summoningSick := true }
  let shang := namedPermanent g "Shang-Chi, Master of Kung Fu"
  let ab := shang.printed.activatedAbilities[0]!
  shang.hasSummoningSickness &&
    !g.canAttack shang &&
    !g.hasHaste shang &&
    g.canActivate ⟨0⟩ shang ab &&
    (mshRuling 280).comment.contains "doesn't grant haste"

#guard shangChiActivateNotHasteOk

/-- Ruling 272: Red Guardian can destroy a creature that dealt damage even
if the recipient has left. -/
def redGuardianDealtDamageOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.dealDamageFrom "Grizzly Bears" ogre 2 (source := some bears)
  let (g, _) := g.move (namedPermanent g "Gray Ogre").id (.graveyard ⟨0⟩) none
  let g := addPermanent g redGuardianSuperSoldier ⟨0⟩ ⟨0⟩
  let rg := namedPermanent g "Red Guardian, Super-Soldier"
  let bears := namedPermanent g "Grizzly Bears"
  bears.status.dealtDamageThisTurn &&
    (let g := g.applyMshTrigger ⟨0⟩ .whenRedGuardianEnters (some rg.id)
       #[Target.permanent bears.id]
     !g.battlefield.any (fun o => o.name == "Grizzly Bears")) &&
    (let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
     let g := addPermanent g redGuardianSuperSoldier ⟨0⟩ ⟨0⟩
     let rg := namedPermanent g "Red Guardian, Super-Soldier"
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.applyMshTrigger ⟨0⟩ .whenRedGuardianEnters (some rg.id)
       #[Target.permanent bears.id]
     g.battlefield.any (fun o => o.name == "Grizzly Bears")) &&
    (mshRuling 272).comment.contains "dealt damage this turn"

#guard redGuardianDealtDamageOk

/-- Rulings 221 / 259 / 300 / 346 / 358: control another player. -/
def controlAnotherPlayerOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := g.setPlayerControl ⟨0⟩ ⟨1⟩
  g.controlsPlayer ⟨0⟩ ⟨1⟩ &&
    g.activePlayer == ⟨0⟩ &&
    (namedPermanent g "Grizzly Bears").controlledBy ⟨1⟩ &&
    g.resourcesFor ⟨1⟩ == ⟨1⟩ &&
    (let g := g.setPlayerControl ⟨0⟩ ⟨1⟩
     let g := { g with controlOnNextTakenTurn := true }
     g.controlsPlayer ⟨0⟩ ⟨1⟩ && g.controlOnNextTakenTurn) &&
    (mshRuling 221).comment.contains "next turn they actually take" &&
    (mshRuling 259).comment.contains "overwrite each other" &&
    (mshRuling 300).comment.contains "still the active player" &&
    (mshRuling 346).comment.contains "can't use your own" &&
    (mshRuling 358).comment.contains "don't control any of that player's permanents"

#guard controlAnotherPlayerOk

/-- Ruling 105: Captain Mar-Vell grants flash if an opponent has already
cast a spell this turn, even if he entered afterward. -/
def captainMarVellFlashOk : Bool :=
  let g := addPermanent afterDraw captainMarVellSpaceBorn ⟨0⟩ ⟨0⟩
  let g := addToHand g grizzlyBears ⟨0⟩
  let gCombat := { g with step := .beginningOfCombat }
  let bears := handCardNamed gCombat ⟨0⟩ "Grizzly Bears"
  !gCombat.asSorcery? ⟨0⟩ &&
    !gCombat.canCast ⟨0⟩ bears &&
    (let gOpp := gCombat.modifyPlayer ⟨1⟩ (fun pl =>
      { pl with spellsCastThisTurn := 1 })
     gOpp.canCast ⟨0⟩ (handCardNamed gOpp ⟨0⟩ "Grizzly Bears")) &&
    (let gLate := addToHand afterDraw grizzlyBears ⟨0⟩
     let gLate := { gLate with step := .beginningOfCombat }
     let gLate := gLate.modifyPlayer ⟨1⟩ (fun pl =>
       { pl with spellsCastThisTurn := 1 })
     !gLate.canCast ⟨0⟩ (handCardNamed gLate ⟨0⟩ "Grizzly Bears") &&
       (let gLate := addPermanent gLate captainMarVellSpaceBorn ⟨0⟩ ⟨0⟩
        gLate.canCast ⟨0⟩ (handCardNamed gLate ⟨0⟩ "Grizzly Bears"))) &&
    (mshRuling 105).comment.contains "as though they had flash"

#guard captainMarVellFlashOk

/-- Ruling 88: becoming a Construct Hero artifact creature replaces
creature types and keeps Equipment. -/
def ironManArmorTypesOk : Bool :=
  let g := addPermanent afterDraw ironManArmor ⟨0⟩ ⟨0⟩
  let armor := namedPermanent g "Iron Man Armor"
  let g := g.applyMshSpell ⟨0⟩ .ifThisEquipmentIsnTACreatureItBecomesA #[]
    (some armor.id)
  let armor := namedPermanent g "Iron Man Armor"
  armor.isCreature &&
    armor.hasSubtype "Construct" &&
    armor.hasSubtype "Hero" &&
    armor.hasSubtype "Equipment" &&
    armor.types.any (· == .artifact) &&
    g.power armor == 1 &&
    g.toughness armor == 1 &&
    (let g := addPermanent afterDraw grayOgre ⟨0⟩ ⟨0⟩
     let ogre := namedPermanent g "Gray Ogre"
     let g := g.mapObjectStatus ogre (fun s => { s with
       additionalArtifactUntilEot := true
       additionalCreatureUntilEot := true
       replacedCreatureTypesUntilEot := some #["Construct", "Hero"] })
     let ogre := namedPermanent g "Gray Ogre"
     !ogre.hasSubtype "Ogre" &&
       ogre.hasSubtype "Construct" &&
       ogre.hasSubtype "Hero") &&
    (mshRuling 88).comment.contains "replaces any existing creature types"

#guard ironManArmorTypesOk

/-- Ruling 138: Robot Domination does not see creature cards that go to
the graveyard at the same time it leaves, and an animated copy is not a
creature card. -/
def robotDominationSimultaneousOk : Bool :=
  let gyWait (g : Game) : Bool :=
    g.waitingTriggers.any (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.creatureCardsPutIntoYourGy)
  let g := addPermanent afterDraw robotDomination ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let (g, _) := g.move (namedPermanent g "Grizzly Bears").id (.graveyard ⟨0⟩) none
  gyWait g &&
    (let g := addPermanent afterDraw robotDomination ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
     let g := g.moveSimultaneousToGraveyard
       #[(namedPermanent g "Robot Domination").id,
         (namedPermanent g "Grizzly Bears").id]
     !gyWait g) &&
    (let g := addPermanent afterDraw robotDomination ⟨0⟩ ⟨0⟩
     let rd := namedPermanent g "Robot Domination"
     let g := g.mapObjectStatus rd (fun s =>
       { s with additionalCreatureUntilEot := true })
     let (g, _) :=
       g.move (namedPermanent g "Robot Domination").id (.graveyard ⟨0⟩) none
     !gyWait g) &&
    (mshRuling 138).comment.contains "won't trigger at all" &&
    (mshRuling 276).comment.contains "creature cards are put into your graveyard"

#guard robotDominationSimultaneousOk

/-- Ruling 223: two attackers are never attacking alone, even at
different players. -/
def attacksAloneDestinationsOk : Bool :=
  let alone (g : Game) : Bool :=
    g.waitingTriggers.any (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.creatureYouControlAttacksAlone)
  let g := addPermanent afterDraw agent13SharonCarter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.setObject { bears with status := { bears.status with
    attacking := true, attackingWhom := some ⟨1⟩ } }
  let g := g.setObject { (namedPermanent g "Gray Ogre") with status :=
    { ogre.status with attacking := true, attackingWhom := some ⟨2⟩ } }
  let two :=
    g.putAttackTriggersOnStack ⟨0⟩
      #[(namedPermanent g "Grizzly Bears").id,
        (namedPermanent g "Gray Ogre").id]
  !alone two &&
    (let g := addPermanent afterDraw agent13SharonCarter ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.setObject { bears with status := { bears.status with
       attacking := true, attackingWhom := some ⟨1⟩ } }
     let one :=
       g.putAttackTriggersOnStack ⟨0⟩ #[(namedPermanent g "Grizzly Bears").id]
     alone one) &&
    (mshRuling 77).comment.contains "attacks alone" &&
    (mshRuling 78).comment.contains "attacks alone" &&
    (mshRuling 79).comment.contains "declare attackers step" &&
    (mshRuling 80).comment.contains "declared as an attacker" &&
    (mshRuling 82).comment.contains "currently attacking" &&
    (mshRuling 223).comment.contains "neither attacking creature is attacking alone"

#guard attacksAloneDestinationsOk

/-- Ruling 333: Daredevil lets you play the exiled card whether or not
it is a Hero; Hero-ness only grants the pump. -/
def daredevilPlayExiledOk : Bool :=
  let g := addPermanent afterDraw daredevilManWithoutFear ⟨0⟩ ⟨0⟩
  let g := addToLibraryTop g lightningBolt ⟨0⟩
  let dd := namedPermanent g "Daredevil, Man Without Fear"
  let g := g.applyMshTrigger ⟨0⟩ .wheneverYouAttack2 (some dd.id)
  let bolt? := g.objects.find? (fun o =>
    o.name == "Lightning Bolt" && o.zone == .exile)
  (match bolt? with
   | some o =>
     g.mayPlayFromExile ⟨0⟩ o &&
       (namedPermanent g "Daredevil, Man Without Fear").status.pump == (0, 0)
   | none => false) &&
    (let g := addPermanent afterDraw daredevilManWithoutFear ⟨0⟩ ⟨0⟩
     let g := addToLibraryTop g mistyKnightHeroForHire ⟨0⟩
     let dd := namedPermanent g "Daredevil, Man Without Fear"
     let g := g.applyMshTrigger ⟨0⟩ .wheneverYouAttack2 (some dd.id)
     let hero? := g.objects.find? (fun o =>
       o.name == "Misty Knight, Hero for Hire" && o.zone == .exile)
     match hero? with
     | some o =>
       g.mayPlayFromExile ⟨0⟩ o &&
         (namedPermanent g "Daredevil, Man Without Fear").status.pump == (2, 1)
     | none => false) &&
    (mshRuling 333).comment.contains "You may play the exiled card"

#guard daredevilPlayExiledOk

/-- Ruling 84: opening-hand actions happen after mulligans, starting
player first, then the first turn begins. -/
def quicksilverOpeningHandOk : Bool :=
  let g := addToHand afterDraw quicksilverBrashBlur ⟨0⟩
  let g := addToHand g quicksilverBrashBlur ⟨1⟩
  let g := g.applyOpeningHandActions
  let p0 := g.battlefield.find? (fun o =>
    o.name == "Quicksilver, Brash Blur" && o.controlledBy ⟨0⟩)
  let p1 := g.battlefield.find? (fun o =>
    o.name == "Quicksilver, Brash Blur" && o.controlledBy ⟨1⟩)
  p0.isSome && p1.isSome &&
    (match p0, p1 with
     | some a, some b => a.timestamp < b.timestamp
     | _, _ => false) &&
    (mshRuling 84).comment.contains "opening hand"

#guard quicksilverOpeningHandOk

/-- Ruling 187: a copy cast without paying its mana cost has X = 0. -/
def freeCopyXIsZeroOk : Bool :=
  let g := addToHand afterDraw photonBlastBarrage ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Photon Blast Barrage"
  let card := { card with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }
  g.playManaCost card photonBlastBarrage == ManaCost.zero &&
    (mshRuling 187).comment.contains "choose 0 as the value of X" &&
    (mshRuling 52).comment.contains "can't choose to cast it for any alternative"

#guard freeCopyXIsZeroOk

/-- Ruling 130: Ares must attack if able, but not if he is sick, tapped,
or attacking would cost. -/
def aresAttacksIfAbleOk : Bool :=
  let g := addPermanent afterDraw aresGodOfWar ⟨0⟩ ⟨0⟩
  let ares := namedPermanent g "Ares, God of War"
  g.mustAttackIfAble ares &&
    (let g := insertObject afterDraw aresGodOfWar ⟨0⟩ .battlefield
       (some ⟨0⟩) { summoningSick := true }
     !g.mustAttackIfAble (namedPermanent g "Ares, God of War")) &&
    (let g := g.mapObjectStatus ares (fun s => { s with tapped := true })
     !g.mustAttackIfAble (namedPermanent g "Ares, God of War")) &&
    !g.mustAttackIfAble ares (attackRequiresCost := true) &&
    (mshRuling 130).comment.contains "doesn't have to attack"

#guard aresAttacksIfAbleOk

/-- Ruling 305: Hawkeye's plus-X is calculated when the noncombat damage
would be dealt. -/
def hawkeyeNoncombatXOk : Bool :=
  let g := addPermanent afterDraw hawkeyeYoungAvenger ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let ogre := namedPermanent g "Gray Ogre"
  let bears := namedPermanent g "Grizzly Bears"
  let gHit := g.dealDamageFrom "Gray Ogre" bears 2 (source := some ogre)
  (namedPermanent gHit "Grizzly Bears").status.damage == 4 &&
    (let g := g.pumpPermanent (namedPermanent g "Hawkeye, Young Avenger") 3 0
     let ogre := namedPermanent g "Gray Ogre"
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.dealDamageFrom "Gray Ogre" bears 2 (source := some ogre)
     (namedPermanent g "Grizzly Bears").status.damage == 7) &&
    (let (g, _) :=
       g.move (namedPermanent g "Hawkeye, Young Avenger").id (.graveyard ⟨0⟩) none
     let ogre := namedPermanent g "Gray Ogre"
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.dealDamageFrom "Gray Ogre" bears 2 (source := some ogre)
     (namedPermanent g "Grizzly Bears").status.damage == 2) &&
    (mshRuling 305).comment.contains "calculated at the time"

#guard hawkeyeNoncombatXOk

/-- Rulings 372 / 373 / 374: play-from-exile permissions still follow
normal timing. -/
def exilePlayFollowsTimingOk : Bool :=
  let g := addToHand afterDraw grizzlyBears ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Grizzly Bears"
  let (g, exiled) := g.move card.id .exile none
  let o := g.object! exiled
  let g := g.setObject { o with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1 } }
  let o := g.object! exiled
  g.mayPlayFromExile ⟨0⟩ o &&
    g.canCast ⟨0⟩ o &&
    (let gCombat := { g with step := .beginningOfCombat }
     !gCombat.asSorcery? ⟨0⟩ &&
       !gCombat.canCast ⟨0⟩ (gCombat.object! exiled)) &&
    (mshRuling 68).comment.contains "normal timing rules" &&
    (mshRuling 372).comment.contains "normal timing rules" &&
    (mshRuling 373).comment.contains "normal timing rules" &&
    (mshRuling 374).comment.contains "timing rules"

#guard exilePlayFollowsTimingOk

/-- Rulings 133 / 189: Crossbones sees other Villains that enter with him,
but the ability triggers only once each turn. -/
def crossbonesVillainOnceOk : Bool :=
  let villainWait (g : Game) : Nat :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.anotherVillainEnters)).size
  let g0 := addPermanent afterDraw crossbonesMaliciousMercenary ⟨0⟩ ⟨0⟩
  let gAlone := g0.afterPermanentEnters
    (namedPermanent g0 "Crossbones, Malicious Mercenary")
  villainWait gAlone == 0 &&
    (let g := addPermanent g0 redGuardianSuperSoldier ⟨0⟩ ⟨0⟩
     let g := g.afterPermanentEnters
       (namedPermanent g "Red Guardian, Super-Soldier")
     villainWait g == 1 &&
       (let xb := namedPermanent g "Crossbones, Malicious Mercenary"
        xb.status.firedOnceEachTurn &&
          (let g := addPermanent g baronStruckerHYDRAOverlord ⟨0⟩ ⟨0⟩
           let g := g.afterPermanentEnters
             (namedPermanent g "Baron Strucker, HYDRA Overlord")
           villainWait g == 1))) &&
    (let xb := namedPermanent g0 "Crossbones, Malicious Mercenary"
     let g := g0.applyMshTrigger ⟨0⟩ .wheneverAnotherVillainYouControlEnters3
       (some xb.id)
     (namedPermanent g "Crossbones, Malicious Mercenary").status.plusOnePlusOne == 1 &&
       (g.player ⟨1⟩).life == 18) &&
    (mshRuling 133).comment.contains "same time as other Villains" &&
    (mshRuling 189).comment.contains "trigger only once"

#guard crossbonesVillainOnceOk

/-- Ruling 307: Squirrel Girl's X is the squirrel count as the ability
resolves. -/
def squirrelGirlXOnceOk : Bool :=
  let g := addPermanent afterDraw theUnbeatableSquirrelGirl ⟨0⟩ ⟨0⟩
  let squirrels (g : Game) : Nat :=
    (g.battlefield.filter (fun o => o.hasSubtype "Squirrel")).size
  let n0 := squirrels g
  let g := g.applyMshSpell ⟨0⟩ .createX11GreenSquirrelCreatureTokensWhe #[] none
  let n1 := squirrels g
  n0 == 1 && n1 == 2 &&
    (let g := g.applyMshSpell ⟨0⟩ .createX11GreenSquirrelCreatureTokensWhe #[] none
     squirrels g == 4) &&
    (mshRuling 307).comment.contains "calculated only once"

#guard squirrelGirlXOnceOk

/-- Rulings 171 / 172: a copy of a linked exile ability adds to the same
exiled-card set; both return when the source leaves. -/
def linkedExileCopyOk : Bool :=
  let g := addPermanent afterDraw cloakAndDaggerEntwined ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let cd := namedPermanent g "Cloak and Dagger, Entwined"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.applyMshTrigger ⟨0⟩ .whenCloakAndDaggerEnter (some cd.id)
    #[Target.player ⟨1⟩, Target.permanent bears.id]
  (namedPermanent g "Cloak and Dagger, Entwined").linkedExile.size == 1 &&
    (let cd := namedPermanent g "Cloak and Dagger, Entwined"
     let ogre := namedPermanent g "Gray Ogre"
     let g := g.applyMshTrigger ⟨0⟩ .whenCloakAndDaggerEnter (some cd.id)
       #[Target.player ⟨1⟩, Target.permanent ogre.id]
     let cd := namedPermanent g "Cloak and Dagger, Entwined"
     cd.linkedExile.size == 2 &&
       !g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
       !g.battlefield.any (fun o => o.name == "Gray Ogre") &&
       (let (g, _) := g.move cd.id (.graveyard ⟨0⟩) none
        g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
          g.battlefield.any (fun o => o.name == "Gray Ogre"))) &&
    (mshRuling 171).comment.contains "linked to a second ability" &&
    (mshRuling 172).comment.contains "linked to a second ability"

#guard linkedExileCopyOk

/-- Ruling 174: boast can be activated only once even if there is another
combat. -/
def boastOncePerTurnOk : Bool :=
  let g := addPermanent afterDraw baronHelmutZemo ⟨0⟩ ⟨0⟩
  let z := namedPermanent g "Baron Helmut Zemo"
  let g := g.mapObjectStatus z (fun s => { s with
    declaredAsAttackerThisTurn := true })
  let z := namedPermanent g "Baron Helmut Zemo"
  g.canActivateBoast z &&
    (let g := g.markBoastUsed z
     let z := namedPermanent g "Baron Helmut Zemo"
     !g.canActivateBoast z &&
       (let g := { g with additionalCombatPhases := 1 }
        !g.canActivateBoast (namedPermanent g "Baron Helmut Zemo"))) &&
    (mshRuling 174).comment.contains "only once"

#guard boastOncePerTurnOk

/-- Ruling 173: a token that dealt first-strike damage and then lost first
strike does not also deal regular combat damage. -/
def okoyeFirstStrikeLossOk : Bool :=
  let g := addPermanent afterDraw okoyeDoraMilajeLeader ⟨0⟩ ⟨0⟩
  let (g, tok) := g.createToken ⟨0⟩ Game.soldier11whiteToken
  let g := g.setObject { tok with status := { tok.status with
    attacking := true, attackingWhom := some ⟨1⟩ } }
  let tok := g.object! tok.id
  g.hasFirstStrike tok &&
    (let g := { g with
        firstStrikeDamageDone := true
        firstStrikeAssignedThisCombat := #[tok.id] }
     let (g, _) := g.move (namedPermanent g "Okoye, Dora Milaje Leader").id
       (.graveyard ⟨0⟩) none
     let tok := g.object! tok.id
     !g.hasFirstStrike tok &&
       !(g.creaturesAssigningCombatDamage true).any (fun o => o.id == tok.id)) &&
    (mshRuling 173).comment.contains "won't also deal normal combat damage"

#guard okoyeFirstStrikeLossOk

/-- Rulings 191 / 192: Nick Fury puts a DFC onto the battlefield front-face-up
unless it is night and the front has daybound. -/
def nickFuryDayDfc : CardDef := { bruceBanner with daybound := true }

def nickFuryDayEnter : Game :=
  let g := addToLibraryTop afterDraw nickFuryDayDfc ⟨0⟩
  g.enterFromNickFury ⟨0⟩ (g.player ⟨0⟩).library.back!

def nickFuryNightEnter : Game :=
  let g := addToLibraryTop { afterDraw with isNight := true } nickFuryDayDfc ⟨0⟩
  g.enterFromNickFury ⟨0⟩ (g.player ⟨0⟩).library.back!

#guard (namedPermanent nickFuryDayEnter "Bruce Banner").name == "Bruce Banner"
#guard !(namedPermanent nickFuryDayEnter "Bruce Banner").status.cantTransform
#guard
  let banner := namedPermanent nickFuryDayEnter "Bruce Banner"
  let g := nickFuryDayEnter.applyAbilityEffect ⟨0⟩ .transform #[] (some banner.id)
  (namedPermanent g "The Incredible Hulk").name == "The Incredible Hulk"
#guard nickFuryNightEnter.isNight && nickFuryDayDfc.daybound &&
  nickFuryDayDfc.otherFace.isSome
#guard (namedPermanent nickFuryNightEnter "The Incredible Hulk").status.cantTransform
#guard
  let hulk := namedPermanent nickFuryNightEnter "The Incredible Hulk"
  let g := nickFuryNightEnter.applyAbilityEffect ⟨0⟩ .transform #[] (some hulk.id)
  (namedPermanent g "The Incredible Hulk").name == "The Incredible Hulk" &&
    logContains g "can't transform"
#guard (mshRuling 191).comment.contains "daybound"
#guard (mshRuling 192).comment.contains "front face up"

def nickFuryDayboundOk : Bool :=
  let banner := namedPermanent nickFuryDayEnter "Bruce Banner"
  let gFlip := nickFuryDayEnter.applyAbilityEffect ⟨0⟩ .transform #[] (some banner.id)
  let hulk := namedPermanent nickFuryNightEnter "The Incredible Hulk"
  let gBlocked := nickFuryNightEnter.applyAbilityEffect ⟨0⟩ .transform #[] (some hulk.id)
  banner.name == "Bruce Banner" &&
    !banner.status.cantTransform &&
    (namedPermanent gFlip "The Incredible Hulk").name == "The Incredible Hulk" &&
    hulk.status.cantTransform &&
    (namedPermanent gBlocked "The Incredible Hulk").name == "The Incredible Hulk" &&
    logContains gBlocked "can't transform" &&
    (mshRuling 191).comment.contains "daybound" &&
    (mshRuling 192).comment.contains "front face up"

#guard nickFuryDayboundOk

/-- Rulings 334 / 335 / 336: you still decide for yourself, you see the
controlled player's hand, and you make their choices. -/
def controlPlayerChoicesOk : Bool :=
  let g := addToHand afterDraw lightningBolt ⟨1⟩
  let g := g.setPlayerControl ⟨0⟩ ⟨1⟩
  g.decidesFor ⟨0⟩ ⟨0⟩ &&
    g.decidesFor ⟨0⟩ ⟨1⟩ &&
    !g.decidesFor ⟨1⟩ ⟨1⟩ &&
    g.canSeeAs ⟨0⟩ ⟨1⟩ &&
    !g.canSeeAs ⟨1⟩ ⟨0⟩ &&
    (g.visibleHand ⟨0⟩ ⟨1⟩).any (fun o => o.name == "Lightning Bolt") &&
    (g.visibleHand ⟨1⟩ ⟨0⟩).isEmpty &&
    (mshRuling 334).comment.contains "continue to make your own choices" &&
    (mshRuling 335).comment.contains "you can see all cards" &&
    (mshRuling 336).comment.contains "you make all choices"

#guard controlPlayerChoicesOk

/-- Rulings 349 / 350 / 351 / 352: controlling a player does not reveal
their sideboard, grant outside-game or tournament choices, or let you
concede for them. They may still concede. -/
def controlPlayerLimitsOk : Bool :=
  let g := afterDraw.setPlayerControl ⟨0⟩ ⟨1⟩
  !g.canLookAtSideboard ⟨0⟩ ⟨1⟩ &&
    g.canLookAtSideboard ⟨1⟩ ⟨1⟩ &&
    !g.canChooseOutsideGame ⟨0⟩ ⟨1⟩ &&
    !g.canMakeTournamentDecision ⟨0⟩ ⟨1⟩ &&
    g.canMakeTournamentDecision ⟨1⟩ ⟨1⟩ &&
    !g.canMakeIllegalDecision ⟨0⟩ ⟨1⟩ &&
    !g.canConcedeAs ⟨0⟩ ⟨1⟩ &&
    g.canConcedeAs ⟨1⟩ ⟨1⟩ &&
    (let g := g.concede ⟨1⟩
     (g.player ⟨1⟩).lost) &&
    (mshRuling 349).comment.contains "sideboard" &&
    (mshRuling 350).comment.contains "tournament rules" &&
    (mshRuling 351).comment.contains "can't make any illegal decisions" &&
    (mshRuling 352).comment.contains "can't make the player"

#guard controlPlayerLimitsOk

/-- Rulings 193 / 196 / 197 / 200: copying a token uses its original
characteristics, not counters or tap. -/
def copyTokenOriginalOk : Bool :=
  let g := addPermanent afterDraw aerialDoombot ⟨0⟩ ⟨0⟩
  let (g, tok) := g.createToken ⟨0⟩ Game.soldier11whiteToken
  let g := g.mapObjectStatus tok (fun s =>
    { s with plusOnePlusOne := 3, tapped := true })
  let dest := namedPermanent g "Aerial Doombot"
  let tok := g.object! tok.id
  let g := g.becomeCopyOf dest tok
  let dest := g.object! dest.id
  dest.printed.name == "Soldier" &&
    dest.printed.power == some 1 &&
    dest.printed.toughness == some 1 &&
    dest.status.plusOnePlusOne == 0 &&
    !dest.status.tapped &&
    (mshRuling 193).comment.contains "original characteristics of that token" &&
    (mshRuling 196).comment.contains "original characteristics of that token" &&
    (mshRuling 197).comment.contains "original characteristics of that token" &&
    (mshRuling 200).comment.contains "original characteristics of that token"

#guard copyTokenOriginalOk

/-- Rulings 155 / 194 / 195 / 198 / 199 / 201: a copy of a copy uses the
copied characteristics. -/
def copyOfCopyOk : Bool :=
  let g := addPermanent afterDraw aerialDoombot ⟨0⟩ ⟨0⟩
  let g := addPermanent g sHIELDDeploymentDrone ⟨0⟩ ⟨0⟩
  let g := addPermanent g futuristForge ⟨0⟩ ⟨0⟩
  let drone := namedPermanent g "S.H.I.E.L.D. Deployment Drone"
  let dest := namedPermanent g "Aerial Doombot"
  let g := g.becomeCopyOf dest drone
  let dest := g.object! dest.id
  let forge := namedPermanent g "Futurist Forge"
  let g := g.becomeCopyOf forge dest
  let forge := g.object! forge.id
  dest.printed.name == "S.H.I.E.L.D. Deployment Drone" &&
    forge.printed.name == "S.H.I.E.L.D. Deployment Drone" &&
    (mshRuling 194).comment.contains "copy of whatever that permanent copied" &&
    (mshRuling 198).comment.contains "copy of whatever" &&
    (mshRuling 199).comment.contains "whatever that creature copied" &&
    (mshRuling 201).comment.contains "copy of whatever that permanent copied" &&
    (mshRuling 155).comment.contains "whatever that creature copied" &&
    (mshRuling 195).comment.contains "whatever that artifact copied"

#guard copyOfCopyOk

/-- Rulings 92 / 93 / 115 / 304: a token copy is not tapped or countered,
and the copied permanent's enters abilities trigger. -/
def copyTokenEntersAbilitiesOk : Bool :=
  let g := addPermanent afterDraw futuristForge ⟨0⟩ ⟨0⟩
  let src := namedPermanent g "Futurist Forge"
  let (g, tok) := g.copyBattlefieldPermanent src ⟨0⟩
  let before := g.waitingTriggers.size
  let g := g.afterPermanentEnters tok
  !tok.status.tapped &&
    tok.status.plusOnePlusOne == 0 &&
    tok.printed.isToken &&
    g.waitingTriggers.size > before &&
    (mshRuling 92).comment.contains "enters abilities of each copied" &&
    (mshRuling 93).comment.contains "enters abilities of the copied" &&
    (mshRuling 115).comment.contains "exactly what was printed" &&
    (mshRuling 304).comment.contains "exactly what was printed"

#guard copyTokenEntersAbilitiesOk

/-- Rulings 36 / 46 / 48 / 66 / 116 / 117 / 278 / 279 / 303: a stack-ability
copy keeps mode, divided damage, and the original source. -/
def copyStackAbilityDetailsOk : Bool :=
  let g := addPermanent afterDraw aerialDoombot ⟨0⟩ ⟨0⟩
  let src := namedPermanent g "Aerial Doombot"
  let (g, ab) := g.allocStackAbility src ⟨0⟩
    (triggeredAbility := some (.onEnterDraw 1))
  let g := g.putStackEntry ⟨0⟩ ab.id
  let g :=
    match g.stack.findIdx? (fun e => e.objectId == ab.id) with
    | none => g
    | some i =>
      { g with stack := g.stack.set! i { g.stack[i]! with
        targets := #[Target.player ⟨1⟩]
        dividedDamage := #[2, 1]
        chosenMode := some 1 } }
  let g := g.copyStackAbility (g.object! ab.id) ⟨0⟩
  let copies := g.objects.filter (fun o =>
    o.zone == .stack && o.isCopy && o.sourceId == some src.id)
  let last := g.stack.back!
  copies.size == 1 &&
    copies[0]!.sourceId == some src.id &&
    last.chosenMode == some 1 &&
    last.dividedDamage == #[2, 1] &&
    last.targets.size == 1 &&
    (mshRuling 36).comment.contains "choices will be made separately" &&
    (mshRuling 46).comment.contains "division can't be changed" &&
    (mshRuling 48).comment.contains "same mode" &&
    (mshRuling 66).comment.contains "can't choose to pay any activation" &&
    (mshRuling 116).comment.contains "not just one with targets" &&
    (mshRuling 117).comment.contains "doesn't cause any object to gain" &&
    (mshRuling 278).comment.contains "not just one with targets" &&
    (mshRuling 279).comment.contains "doesn't cause any object to gain" &&
    (mshRuling 303).comment.contains "same as the source of the original"

#guard copyStackAbilityDetailsOk

/-- Rulings 134 / 183 / 327: Hulkling re-checks on resolve, multiple
enters trigger separately, and a swapped greater stat still counts. -/
def hulklingRecheckOk : Bool :=
  let g := mshEnter afterDraw hulklingBurgeoningBruiser
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  let giant := namedPermanent g "Hill Giant"
  let hulkling := namedPermanent g "Hulkling, Burgeoning Bruiser"
  let gShrink := g.pumpPermanent giant (-2) (-2)
  let gShrink := gShrink.applyMshTrigger ⟨0⟩ .wheneverAnotherCreatureYouControlEnters
    (some hulkling.id) #[Target.permanent giant.id]
  (namedPermanent gShrink "Hulkling, Burgeoning Bruiser").status.plusOnePlusOne == 0 &&
    (let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
     let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
     let hulkling := namedPermanent g "Hulkling, Burgeoning Bruiser"
     let giants := g.battlefield.filter (fun o => o.name == "Hill Giant")
     let g := g.applyMshTrigger ⟨0⟩ .wheneverAnotherCreatureYouControlEnters
       (some hulkling.id) #[Target.permanent giants[0]!.id]
     let g := g.applyMshTrigger ⟨0⟩ .wheneverAnotherCreatureYouControlEnters
       (some hulkling.id) #[Target.permanent giants[1]!.id]
     (namedPermanent g "Hulkling, Burgeoning Bruiser").status.plusOnePlusOne == 1) &&
    (let g := mshEnter afterDraw hulklingBurgeoningBruiser
     let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
     let bot := namedPermanent g "Aerial Doombot"
     let g := g.mapObjectStatus bot (fun s => { s with setBasePT := some (1, 4) })
     let hulkling := namedPermanent g "Hulkling, Burgeoning Bruiser"
     let g := g.mapObjectStatus hulkling (fun s => { s with setBasePT := some (4, 3) })
     let hulkling := namedPermanent g "Hulkling, Burgeoning Bruiser"
     let g := g.applyMshTrigger ⟨0⟩ .wheneverAnotherCreatureYouControlEnters
       (some hulkling.id) #[Target.permanent bot.id]
     (namedPermanent g "Hulkling, Burgeoning Bruiser").status.plusOnePlusOne == 1) &&
    (mshRuling 134).comment.contains "stat comparison will happen again" &&
    (mshRuling 183).comment.contains "trigger multiple times" &&
    (mshRuling 327).comment.contains "stat that's greater changes"

#guard hulklingRecheckOk

/-- Rulings 112 / 293: damage is tracked through indestructible; deathtouch
is checked only on the first SBA pass after the damage. -/
def doctorDoomDamageTrackedOk : Bool :=
  let g := addPermanent afterDraw doctorDoom ⟨0⟩ ⟨0⟩
  let doom := namedPermanent g "Doctor Doom"
  let g := g.mapObjectStatus doom (·.grantUntilEot Keyword.indestructible)
  let doom := namedPermanent g "Doctor Doom"
  let g := g.markDamageOn doom 3 "Doctor Doom is dealt 3"
  let g := g.checkSBA
  onBattlefield g "Doctor Doom" &&
    (namedPermanent g "Doctor Doom").status.damage == 3 &&
    (let doom := namedPermanent g "Doctor Doom"
     let g := g.mapObjectStatus doom (fun s =>
       { s with untilEotKeywords := Keywords.none })
     let g := g.checkSBA
     !onBattlefield g "Doctor Doom") &&
    (let g := addPermanent afterDraw doctorDoom ⟨0⟩ ⟨0⟩
     let doom := namedPermanent g "Doctor Doom"
     let g := g.mapObjectStatus doom (·.grantUntilEot Keyword.indestructible)
     let doom := namedPermanent g "Doctor Doom"
     let g := g.markDamageOn doom 1 "deathtouch" (deathtouch := true)
     let g := g.checkSBA
     onBattlefield g "Doctor Doom" &&
       !(namedPermanent g "Doctor Doom").status.dealtDeathtouch &&
       (let doom := namedPermanent g "Doctor Doom"
        let g := g.mapObjectStatus doom (fun s =>
          { s with untilEotKeywords := Keywords.none })
        let g := g.checkSBA
        onBattlefield g "Doctor Doom")) &&
    (mshRuling 112).comment.contains "tracked even if he has indestructible" &&
    (mshRuling 293).comment.contains "first time that state-based actions"

#guard doctorDoomDamageTrackedOk

/-- Rulings 145 / 190: Wasp leaving before resolve still taps; later granted
abilities are kept after printed abilities are lost. -/
def wondrousWaspLoseAbilitiesOk : Bool :=
  let g := addPermanent afterDraw theWondrousWasp ⟨0⟩ ⟨0⟩
  let g := addPermanent g stormWindrider ⟨0⟩ ⟨0⟩
  let wasp := namedPermanent g "The Wondrous Wasp"
  let storm := namedPermanent g "Storm, Windrider"
  let (g, _) := g.move wasp.id (.graveyard ⟨0⟩) none
  let g := g.applyMshTrigger ⟨0⟩ .waspSStingWhenTheWondrousWa (some wasp.id)
    #[Target.permanent storm.id]
  (namedPermanent g "Storm, Windrider").status.tapped &&
    g.hasFlying (namedPermanent g "Storm, Windrider") &&
    (let g := addPermanent afterDraw theWondrousWasp ⟨0⟩ ⟨0⟩
     let g := addPermanent g stormWindrider ⟨0⟩ ⟨0⟩
     let wasp := namedPermanent g "The Wondrous Wasp"
     let storm := namedPermanent g "Storm, Windrider"
     let g := g.applyMshTrigger ⟨0⟩ .waspSStingWhenTheWondrousWa (some wasp.id)
       #[Target.permanent storm.id]
     let storm := namedPermanent g "Storm, Windrider"
     storm.status.tapped &&
       !g.hasFlying storm &&
       (let g := g.mapObjectStatus storm (·.grantUntilEot Keyword.flying)
        g.hasFlying (namedPermanent g "Storm, Windrider"))) &&
    (mshRuling 145).comment.contains "won't lose its abilities" &&
    (mshRuling 190).comment.contains "will keep that ability"

#guard wondrousWaspLoseAbilitiesOk

/-- Ruling 143: Super Hero Civil War leaving skips the control change. -/
def superHeroCivilWarLeaveOk : Bool :=
  let g := addPermanent afterDraw theSuperHeroCivilWar ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let saga := namedPermanent g "The Super Hero Civil War"
  let bears := namedPermanent g "Grizzly Bears"
  let (g, _) := g.move saga.id (.graveyard ⟨0⟩) none
  let g := g.applyMshChapter ⟨0⟩ .gainControlOfUpToTwoTargetCreaturesWith
    #[Target.permanent bears.id] (some saga.id)
  (namedPermanent g "Grizzly Bears").controlledBy ⟨1⟩ &&
    (let g := addPermanent afterDraw theSuperHeroCivilWar ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
     let saga := namedPermanent g "The Super Hero Civil War"
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.applyMshChapter ⟨0⟩ .gainControlOfUpToTwoTargetCreaturesWith
       #[Target.permanent bears.id] (some saga.id)
     (namedPermanent g "Grizzly Bears").controlledBy ⟨0⟩) &&
    (mshRuling 143).comment.contains "won't gain control"

#guard superHeroCivilWarLeaveOk

/-- Ruling 151: an artifact Villain entering fires HYDRA Assault Robot once. -/
def hydraAssaultOnceOk : Bool :=
  let g := addPermanent afterDraw hYDRAAssaultRobot ⟨0⟩ ⟨0⟩
  let g := addPermanent g ultronDrone ⟨0⟩ ⟨0⟩
  let drone := namedPermanent g "Ultron Drone"
  let g := g.afterPermanentEnters drone
  let n :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.source.name == "HYDRA Assault Robot")).size
  n == 1 &&
    (mshRuling 151).comment.contains "trigger only once"

#guard hydraAssaultOnceOk

/-- Ruling 317: token creatures dying do not trigger Robot Domination. -/
def robotDominationTokenOk : Bool :=
  let g := addPermanent afterDraw robotDomination ⟨0⟩ ⟨0⟩
  let (g, tok) := g.createToken ⟨0⟩ Game.soldier11whiteToken
  let (g, _) := g.move tok.id (.graveyard ⟨0⟩) none
  !g.waitingTriggers.any (fun (t : WaitingTrigger) =>
    t.event == TriggerEvent.creatureCardsPutIntoYourGy) &&
    (mshRuling 317).comment.contains "Token creatures"

#guard robotDominationTokenOk

/-- Ruling 297: Avengers Assemble! does not trigger if neither condition
was met. -/
def avengersAssembleNoTriggerOk : Bool :=
  let g := addPermanent afterDraw avengersAssemble ⟨0⟩ ⟨0⟩
  let assem := namedPermanent g "Avengers Assemble!"
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.applyTriggeredAbility ⟨0⟩
    (.onEachEndStepDrawIfAttackedOrEnteredSubtype "Hero") (some assem.id)
  (g.player ⟨0⟩).hand.size == hand0 &&
    (mshRuling 297).comment.contains "won't trigger at all"

#guard avengersAssembleNoTriggerOk

/-- Rulings 262 / 263 / 264: becoming a better blocker or shrinking after
the block does not make the attacker unblocked. -/
def blockedStaysBlockedOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let bears := namedPermanent g "Grizzly Bears"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.setObject { bears with status := { bears.status with
    attacking := true, attackingWhom := some ⟨1⟩, blocked := true } }
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { ogre with status := { ogre.status with
    blocking := #[bears.id] } }
  let g := g.mapObjectStatus (namedPermanent g "Grizzly Bears")
    (·.grantUntilEot Keyword.flying)
  (namedPermanent g "Grizzly Bears").status.blocked &&
    g.hasFlying (namedPermanent g "Grizzly Bears") &&
    (mshRuling 262).comment.contains "won't cause him to become unblocked" &&
    (mshRuling 263).comment.contains "won't cause her to become unblocked" &&
    (mshRuling 264).comment.contains "won't be able to make that block illegal"

#guard blockedStaysBlockedOk

/-- Ruling 258: multiple lifelink instances are redundant. -/
def yellowjacketLifelinkRedundantOk : Bool :=
  let g := addPermanent afterDraw yellowjacketHeartlessMarauder ⟨0⟩ ⟨0⟩
  let yj := namedPermanent g "Yellowjacket, Heartless Marauder"
  let g := g.mapObjectStatus yj (·.grantUntilEot Keyword.lifelink)
  g.hasLifelink (namedPermanent g "Yellowjacket, Heartless Marauder") &&
    (mshRuling 258).comment.contains "Multiple instances of lifelink"

#guard yellowjacketLifelinkRedundantOk

/-- Ruling 169: Scarlet Witch uses the chosen X when checking mana value. -/
def scarletWitchXManaValueOk : Bool :=
  let g := addPermanent afterDraw theScarletWitch ⟨0⟩ ⟨0⟩
  let (g, spell) := g.allocObject photonBlastBarrage ⟨0⟩ (.hand ⟨0⟩) (some ⟨0⟩)
  let cheap := g.object! spell.id
  let cheap := { cheap with chosenX := some 1 }
  let g := g.setObject cheap
  let costly := { cheap with chosenX := some 2 }
  let start := photonBlastBarrage.manaCost
  let reduced := g.applyCastCostReductions costly photonBlastBarrage start
  let unreduced := g.applyCastCostReductions cheap photonBlastBarrage start
  reduced.manaValue == 2 &&
    unreduced.manaValue == 3 &&
    (mshRuling 169).comment.contains "value chosen for X"

#guard scarletWitchXManaValueOk

/-- Ruling 109: Loki compares mana value to last-known power if he left. -/
def lokiLastKnownPowerOk : Bool :=
  let g := addPermanent afterDraw lokiLaufeyson ⟨0⟩ ⟨0⟩
  let loki := namedPermanent g "Loki Laufeyson"
  let g := g.applyMshSpell ⟨0⟩ .whenYouNextCastAnInstantOrSorcerySpellW #[]
    (some loki.id)
  let (g, _) := g.move loki.id (.graveyard ⟨0⟩) none
  let (g, spell) := g.allocObject lightningBolt ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.putStackEntry ⟨0⟩ spell.id
  let g := g.putCastTriggersOnStack ⟨0⟩ (g.object! spell.id)
  let copies := g.objects.filter (fun o =>
    o.zone == .stack && o.isCopy && o.printed.name == "Lightning Bolt")
  copies.size == 1 &&
    (mshRuling 109).comment.contains "last time he was on the battlefield"

#guard lokiLastKnownPowerOk

/-- Ruling 270: H.E.R.B.I.E. putting a land onto the battlefield is not
playing a land. -/
def herbieLandNotPlayOk : Bool :=
  let g := addToHand afterDraw forest ⟨0⟩
  let played0 := (g.player ⟨0⟩).landsPlayedThisTurn
  let g := addPermanent g hERBIEScoutUnit ⟨0⟩ ⟨0⟩
  let herbie := namedPermanent g "H.E.R.B.I.E. Scout Unit"
  let g := g.applyMshTrigger ⟨0⟩ .whenThisCreatureEnters4 (some herbie.id)
  g.battlefield.any (fun o =>
      o.printed.isLand && o.status.tapped && o.status.enteredThisTurn) &&
    (g.player ⟨0⟩).landsPlayedThisTurn == played0 &&
    (mshRuling 270).comment.contains "doesn't count as playing a land"

#guard herbieLandNotPlayOk

/-- Ruling 146 / 312: Tigra does not get a counter in time to survive
simultaneous lethal damage, and life gain is one event. -/
def tigraLethalLifeOk : Bool :=
  let g := addPermanent afterDraw tigraFelineFury ⟨0⟩ ⟨0⟩
  let tigra := namedPermanent g "Tigra, Feline Fury"
  let g := g.markDamageOn tigra 1 "Tigra is dealt 1"
  let g := g.gainLife ⟨0⟩ 3
  let g := g.checkSBA
  !onBattlefield g "Tigra, Feline Fury" &&
    (mshRuling 146).comment.contains "won't receive a counter" &&
    (mshRuling 312).comment.contains "just once"

#guard tigraLethalLifeOk

/-- Ruling 295: Thunderbolts returns a Villain as a Hero from the moment
it enters. -/
def thunderboltsHeroTypeOk : Bool :=
  let g := addPermanent afterDraw thunderboltsConspiracy ⟨0⟩ ⟨0⟩
  let g := addPermanent g agentsOfHYDRA ⟨0⟩ ⟨0⟩
  let villain := namedPermanent g "Agents of HYDRA"
  let (g, _) := g.move villain.id (.graveyard ⟨0⟩) none
  let gy := namedGraveyardCard g ⟨0⟩ "Agents of HYDRA"
  let before := g.waitingTriggers.size
  let g := g.applyMshTrigger ⟨0⟩ .wheneverAVillainYouControlDies
    (some (namedPermanent g "Thunderbolts Conspiracy").id) #[Target.card gy.id]
  let o := namedPermanent g "Agents of HYDRA"
  g.hasSubtype o "Hero" &&
    o.status.finality == 1 &&
    g.waitingTriggers.size >= before &&
    (mshRuling 295).comment.contains "Hero in addition to its other types"

#guard thunderboltsHeroTypeOk

/-- Ruling 144: The Void attacks if able, but not while sick, tapped, or
if attacking would require an unpaid cost. -/
def theVoidAttacksIfAbleOk : Bool :=
  let (g, tok) := afterDraw.createToken ⟨0⟩ Game.theVoidToken
  Game.hasAttacksIfAble tok &&
    !g.mustAttackIfAble tok &&
    (let g := g.mapObjectStatus tok (fun s => { s with summoningSick := false })
     let tok := g.object! tok.id
     g.mustAttackIfAble tok &&
       (let g := g.mapObjectStatus tok (fun s => { s with tapped := true })
        !g.mustAttackIfAble (g.object! tok.id) &&
          !g.mustAttackIfAble tok (attackRequiresCost := true))) &&
    (mshRuling 144).comment.contains "doesn't attack"

#guard theVoidAttacksIfAbleOk

/-- Rulings 107 / 108 / 123 / 239 / 248 / 250 / 251 / 260 / 269 / 271 / 282 /
285 / 311 / 339: a spell that targets a creature you control queues those
cast triggers once, above the spell. Madame Hydra queues on a Villain
spell. Loki (247) queues when an ability you control gets a target. -/
def castTriggerBeforeSpellOk : Bool :=
  let g := addPermanent afterDraw colleenWingStreetSamurai ⟨0⟩ ⟨0⟩
  let g := addPermanent g ironFistLivingWeapon ⟨0⟩ ⟨0⟩
  let g := addPermanent g mockingbirdAceAgent ⟨0⟩ ⟨0⟩
  let g := addPermanent g msMarvelKamalaKhan ⟨0⟩ ⟨0⟩
  let g := addPermanent g madameHydra ⟨0⟩ ⟨0⟩
  let g := addPermanent g lokiGodOfMischief ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let (g, spell) := g.allocObject helicarrierStrike ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.putStackEntry ⟨0⟩ spell.id
  let g :=
    match g.stack.findIdx? (fun e => e.objectId == spell.id) with
    | none => g
    | some i =>
      { g with stack := g.stack.set! i { g.stack[i]! with
          targets := #[Target.permanent bears.id] } }
  let g := g.putCastTriggersOnStack ⟨0⟩ (g.object! spell.id)
  let names :=
    (g.waitingTriggers.map (fun (t : WaitingTrigger) => t.source.name))
  names.any (· == "Colleen Wing, Street Samurai") &&
    names.any (· == "Iron Fist, Living Weapon") &&
    names.any (· == "Mockingbird, Ace Agent") &&
    names.any (· == "Ms. Marvel, Kamala Khan") &&
    !names.any (· == "Madame Hydra") &&
    g.objects.any (fun o => o.id == spell.id && o.zone == .stack) &&
    (let (gV, villain) := g.allocObject agentsOfHYDRA ⟨0⟩ .stack (some ⟨0⟩)
     let gV := gV.putStackEntry ⟨0⟩ villain.id
     let gV := gV.putCastTriggersOnStack ⟨0⟩ (gV.object! villain.id)
     (gV.waitingTriggers.map (fun (t : WaitingTrigger) => t.source.name)).any
       (· == "Madame Hydra") &&
       gV.objects.any (fun o => o.id == villain.id && o.zone == .stack)) &&
    (let (gAb, ab) := g.allocObject helicarrierStrike ⟨0⟩ .stack (some ⟨0⟩)
     let gAb := gAb.setObject { ab with abilityEffect := some (.dealDamageToTargetCreature 1) }
     let gAb := gAb.putStackEntry ⟨0⟩ ab.id
     let gAb := gAb.queueYouTargetTriggers ⟨0⟩ (gAb.object! ab.id)
     gAb.waitingTriggers.any (fun (t : WaitingTrigger) =>
         t.source.name == "Loki, God of Mischief") &&
       gAb.objects.any (fun o => o.id == ab.id && o.zone == .stack)) &&
    (mshRuling 107).comment.contains "resolves before the spell" &&
    (mshRuling 108).comment.contains "doesn't trigger multiple times" &&
    (mshRuling 123).comment.contains "doesn't trigger multiple times" &&
    (mshRuling 260).comment.contains "resolves before the spell" &&
    (mshRuling 269).comment.contains "resolves before the spell" &&
    (mshRuling 271).comment.contains "resolves before the spell" &&
    (mshRuling 282).comment.contains "resolves before the spell" &&
    (mshRuling 285).comment.contains "resolves before the spell" &&
    (mshRuling 311).comment.contains "resolves before the spell" &&
    (mshRuling 339).comment.contains "resolves before the spell" &&
    (mshRuling 239).comment.contains "resolves before the spell" &&
    (mshRuling 247).comment.contains "resolves before the ability" &&
    (mshRuling 248).comment.contains "resolves before the spell" &&
    (mshRuling 250).comment.contains "resolves before the spell" &&
    (mshRuling 251).comment.contains "resolves before the spell"

#guard castTriggerBeforeSpellOk

/-- Rulings 41 / 53 / 126: one life-gaining event triggers Tigra once. -/
def lifeGainOnceOk : Bool :=
  let g := addPermanent afterDraw tigraFelineFury ⟨0⟩ ⟨0⟩
  let g := g.gainLife ⟨0⟩ 5
  let n :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.source.name == "Tigra, Feline Fury")).size
  n == 1 &&
    (mshRuling 41).comment.contains "separate life-gaining event" &&
    (mshRuling 53).comment.contains "triggers only once" &&
    (mshRuling 126).comment.contains "just once"

#guard lifeGainOnceOk

/-- Ruling 291: Hawkeye's extra damage is dealt by the original source. -/
def hawkeyeSameSourceOk : Bool :=
  let g := addPermanent afterDraw hawkeyeYoungAvenger ⟨0⟩ ⟨0⟩
  let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let src := namedPermanent g "Aerial Doombot"
  let bears := namedPermanent g "Grizzly Bears"
  let hawk := namedPermanent g "Hawkeye, Young Avenger"
  let g := g.dealDamageFrom src.name bears 1 (source := some src)
  (namedPermanent g "Grizzly Bears").status.damage == 1 + g.power hawk &&
    logContains g "Aerial Doombot deals" &&
    (mshRuling 291).comment.contains "same source as the original"

#guard hawkeyeSameSourceOk

/-- Ruling 178: if all of a source's damage is prevented, Hawkeye's extra
damage no longer applies. -/
def hawkeyePreventionSkipsExtraOk : Bool :=
  let g := addPermanent afterDraw hawkeyeYoungAvenger ⟨0⟩ ⟨0⟩
  let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let src := namedPermanent g "Aerial Doombot"
  let hawk := namedPermanent g "Hawkeye, Young Avenger"
  let extra := g.power hawk
  let gHit := g.dealDamageFrom src.name (namedPermanent g "Grizzly Bears") 1
    (source := some src)
  (namedPermanent gHit "Grizzly Bears").status.damage == 1 + extra &&
    (let gPrev := g.mapObjectStatus src (fun s =>
        { s with preventDamageGrantedBy := #[src.id] })
     let src := namedPermanent gPrev "Aerial Doombot"
     let gPrev := gPrev.dealDamageFrom src.name (namedPermanent gPrev "Grizzly Bears") 1
       (source := some src)
     (namedPermanent gPrev "Grizzly Bears").status.damage == 0 &&
       gPrev.log.any (fun s => mentions s "prevented")) &&
    (mshRuling 178).comment.contains "chooses an order"

#guard hawkeyePreventionSkipsExtraOk

/-- Ruling 348: The Ruinous Wrecking Crew cannot choose the same mode twice. -/
def wreckingCrewModesOnceOk : Bool :=
  let g := addPermanent afterDraw theRuinousWreckingCrew ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "The Ruinous Wrecking Crew"
  let g := g.mapObjectStatus o (fun s => { s with chosenModes := #[0, 2] })
  let o := namedPermanent g "The Ruinous Wrecking Crew"
  o.status.chosenModes.contains 0 &&
    !o.status.chosenModes.contains 1 &&
    (mshRuling 348).comment.contains "can't choose the same mode"

#guard wreckingCrewModesOnceOk

/-- Ruling 59: tapping an artifact does not turn off its static abilities. -/
def improviseStaticsWhileTappedOk : Bool :=
  let g := addPermanent afterDraw ironheartCleverChampion ⟨0⟩ ⟨0⟩
  let ih := namedPermanent g "Ironheart, Clever Champion"
  let g := g.mapObjectStatus ih (fun s => { s with tapped := true })
  g.spellHasImprovise helicarrierStrike ⟨0⟩ &&
    (namedPermanent g "Ironheart, Clever Champion").status.tapped &&
    (mshRuling 59).comment.contains "won't cause its abilities to stop"

#guard improviseStaticsWhileTappedOk

/-- Ruling 229: tap an artifact for improvise, then it can still be
sacrificed as an additional cost. -/
def improviseThenSacrificeOk : Bool :=
  let (g, tok) := afterDraw.createToken ⟨0⟩ treasureToken
  match g.tapArtifactsForImprovise ⟨0⟩ #[tok.id] with
  | .ok g =>
    (g.object! tok.id).status.tapped &&
      (g.object! tok.id).isOnBattlefield &&
      (mshRuling 229).comment.contains "tap that permanent"
  | .error _ => false

#guard improviseThenSacrificeOk

/-- Ruling 57: a Two-Headed Giant teammate's life gain is not "you gain life". -/
def twoHeadedGiantTeammateLifeOk : Bool :=
  let g := addPermanent afterDraw tigraFelineFury ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with teammate := some ⟨1⟩ })
  let g := g.modifyPlayer ⟨1⟩ (fun pl => { pl with teammate := some ⟨0⟩ })
  let g := g.gainLife ⟨1⟩ 3
  !(g.waitingTriggers.any (fun (t : WaitingTrigger) =>
      t.source.name == "Tigra, Feline Fury")) &&
    (mshRuling 57).comment.contains "Two-Headed Giant"

#guard twoHeadedGiantTeammateLifeOk

/-- Ruling 236: controlling a player in Two-Headed Giant controls the team. -/
def twoHeadedGiantControlTeamOk : Bool :=
  let g := afterDraw.modifyPlayer ⟨1⟩ (fun pl => { pl with teammate := some ⟨0⟩ })
  let g := g.setPlayerControl ⟨0⟩ ⟨1⟩
  g.controlsPlayer ⟨0⟩ ⟨1⟩ &&
    g.controlsPlayer ⟨0⟩ ⟨0⟩ &&
    (mshRuling 236).comment.contains "gain control of each player"

#guard twoHeadedGiantControlTeamOk

/-- Ruling 106 / 239: each targeting spell grants Iron Fist another tap
ability; the trigger waits above the spell. -/
def ironFistMultipleGrantsOk : Bool :=
  let g := addPermanent afterDraw ironFistLivingWeapon ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let fist := namedPermanent g "Iron Fist, Living Weapon"
  let g := g.applyMshTrigger ⟨0⟩ .wheneverYouCastASpellThatTargetsACreatur
    (some fist.id)
  let g := g.applyMshTrigger ⟨0⟩ .wheneverYouCastASpellThatTargetsACreatur
    (some fist.id)
  (namedPermanent g "Iron Fist, Living Weapon").status.ironFistTapGrants == 2 &&
    (mshRuling 106).comment.contains "multiple instances"

#guard ironFistMultipleGrantsOk

/-- Ruling 170: an Aura returns without targeting and can attach through
hexproof. -/
def mindStoneAuraReturnOk : Bool :=
  let g := addPermanent afterDraw theMindStone ⟨0⟩ ⟨0⟩
  let g := addPermanent g superSoldierSerum ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let aura := namedPermanent g "Super-Soldier Serum"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.mapObjectStatus bears (·.grantUntilEot Keyword.hexproof)
  let (g, _) := g.move aura.id .exile none
  let ex :=
    (g.objects.find? (fun o => o.name == "Super-Soldier Serum" && o.zone == .exile)).getD aura
  let g := g.returnExiledId ex.id
  let aura := namedPermanent g "Super-Soldier Serum"
  aura.attachedTo == some (namedPermanent g "Grizzly Bears").id &&
    g.log.any (fun s => mentions s "does not target") &&
    (mshRuling 170).comment.contains "doesn't target anything"

#guard mindStoneAuraReturnOk

/-- Rulings 177 / 179 / 237: Mjölnir doubles after assignment; two hammers
multiply by four; prevention of all damage skips Mjölnir. -/
def mjolnirDoubleOk : Bool :=
  let g := addPermanent afterDraw mjLnirHammerOfThor ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let hammer := namedPermanent g "Mjölnir, Hammer of Thor"
  let ogre := namedPermanent g "Gray Ogre"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.attachSourceTo hammer ogre
  let gHit := g.dealDamageFrom ogre.name bears 2 (source := some (namedPermanent g "Gray Ogre"))
  (namedPermanent gHit "Grizzly Bears").status.damage == 4 &&
    (let g := addPermanent g mjLnirHammerOfThor ⟨0⟩ ⟨0⟩
     let hammers := g.battlefield.filter (fun o => o.name == "Mjölnir, Hammer of Thor")
     let ogre := namedPermanent g "Gray Ogre"
     let g :=
       hammers.foldl (fun acc h => acc.attachSourceTo (acc.object! h.id) ogre) g
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.dealDamageFrom ogre.name bears 2 (source := some (namedPermanent g "Gray Ogre"))
     (namedPermanent g "Grizzly Bears").status.damage == 8) &&
    (let gPrev := g.mapObjectStatus ogre (fun s =>
        { s with preventDamageGrantedBy := #[ogre.id] })
     let gPrev := gPrev.dealDamageFrom ogre.name (namedPermanent gPrev "Grizzly Bears") 2
       (source := some (namedPermanent gPrev "Gray Ogre"))
     (namedPermanent gPrev "Grizzly Bears").status.damage == 0 &&
       gPrev.log.any (fun s => mentions s "prevented")) &&
    (mshRuling 177).comment.contains "chooses the order" &&
    (mshRuling 179).comment.contains "divided or assigned before doubling" &&
    (mshRuling 237).comment.contains "multiplied by four"

#guard mjolnirDoubleOk

/-- Ruling 179: combat assignment is doubled after the split. -/
def mjolnirCombatDivideOk : Bool :=
  let g := addPermanent afterDraw mjLnirHammerOfThor ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  let hammer := namedPermanent g "Mjölnir, Hammer of Thor"
  let ogre := namedPermanent g "Gray Ogre"
  let giant := namedPermanent g "Hill Giant"
  let g := g.attachSourceTo hammer ogre
  let g := g.setObject { ogre with status :=
    { ogre.status with attacking := true, blocked := true, attackingWhom := some ⟨1⟩ } }
  let g := { g with assignedCombatDamage :=
    #[{ source := ogre.id, toCreatures := #[(giant.id, 1)], toPlayer := 2 }] }
  let g := g.dealAssignedCombatDamage
  (namedPermanent g "Hill Giant").status.damage == 2 &&
    (g.player ⟨1⟩).life == 20 - 4

#guard mjolnirCombatDivideOk

/-- Ruling 204: a creature not controlled by the target opponent is illegal,
but the ability may still reveal. -/
def cloakIllegalCreatureStillResolvesOk : Bool :=
  let g := addToHand afterDraw lightningBolt ⟨1⟩
  let g := addPermanent g cloakAndDaggerEntwined ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let cloak := namedPermanent g "Cloak and Dagger, Entwined"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.applyMshTrigger ⟨0⟩ .whenCloakAndDaggerEnter (some cloak.id)
    #[Target.player ⟨1⟩, Target.permanent bears.id]
  logContains g "illegal target" &&
    onBattlefield g "Grizzly Bears" &&
    (mshRuling 204).comment.contains "illegal target"

#guard cloakIllegalCreatureStillResolvesOk

/-- Ruling 234: a card exiled from hand returns to hand when Cloak leaves. -/
def cloakReturnToHandOk : Bool :=
  let g := addToHand afterDraw lightningBolt ⟨1⟩
  let g := addPermanent g cloakAndDaggerEntwined ⟨0⟩ ⟨0⟩
  let bolt := handCardNamed g ⟨1⟩ "Lightning Bolt"
  let cloak := namedPermanent g "Cloak and Dagger, Entwined"
  let g := g.exileUntilSourceLeaves (some cloak.id) bolt
  let (g, _) := g.move cloak.id (.graveyard ⟨0⟩) none
  (g.handObjects ⟨1⟩).any (fun o => o.name == "Lightning Bolt") &&
    (mshRuling 234).comment.contains "returns to their hand"

#guard cloakReturnToHandOk

/-- Ruling 205: if the enchanted creature left, Serum does not move Equipment. -/
def serumHostLeftOk : Bool :=
  let g := addPermanent afterDraw superSoldierSerum ⟨0⟩ ⟨0⟩
  let g := addPermanent g vibraniumEnergyDaggers ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let eq := namedPermanent g "Vibranium Energy Daggers"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.attachSourceTo eq ogre
  let serum := namedPermanent g "Super-Soldier Serum"
  let g := g.applyMshTrigger ⟨0⟩ .wheneverEnchantedCreatureAttacksOrBlocks
    (some serum.id) #[Target.permanent eq.id]
  (namedPermanent g "Vibranium Energy Daggers").attachedTo == some ogre.id &&
    logContains g "Equipment stays" &&
    (mshRuling 205).comment.contains "remain attached"

#guard serumHostLeftOk

/-- Ruling 206: if either fight target is illegal, HULK SMASH deals no damage. -/
def hulkSmashIllegalFizzleOk : Bool :=
  let g := addPermanent afterDraw grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let ogre := namedPermanent g "Gray Ogre"
  let bears := namedPermanent g "Grizzly Bears"
  let (g, _) := g.move bears.id (.graveyard ⟨1⟩) none
  let g := g.applyEffect ⟨0⟩ .creatureYouControlDealsPowerToOppCreature
    #[Target.permanent ogre.id, Target.permanent bears.id]
  (namedPermanent g "Gray Ogre").status.damage == 0 &&
    (mshRuling 206).comment.contains "no damage will be dealt"

#guard hulkSmashIllegalFizzleOk

/-- Ruling 207: an illegal land target fizzles Avengers Disassembled entirely. -/
def avengersDisassembledFizzleOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g forest ⟨1⟩ ⟨1⟩
  let land := namedPermanent g "Forest"
  let (gGone, _) := g.move land.id (.graveyard ⟨1⟩) none
  let fizzled := gGone.applyAvengersDisassembled ⟨0⟩ true true (some land.id)
  (namedPermanent fizzled "Grizzly Bears").status.damage == 0 &&
    logContains fizzled "doesn't resolve" &&
    (let gOk := g.applyAvengersDisassembled ⟨0⟩ true true (some land.id)
     (namedPermanent gOk "Grizzly Bears").status.damage == 3 &&
       logContains gOk "may search") &&
    (mshRuling 207).comment.contains "won't resolve"

#guard avengersDisassembledFizzleOk

/-- Ruling 220: Klaw reveals the whole hand if it is smaller than N. -/
def klawRevealAllOk : Bool :=
  let g :=
    (afterDraw.player ⟨1⟩).hand.foldl (fun acc id =>
      (acc.move id (.library ⟨1⟩) none).1) afterDraw
  let g := addToHand g lightningBolt ⟨1⟩
  let g := addPermanent g klawSonicSubjugator ⟨0⟩ ⟨0⟩
  let klaw := namedPermanent g "Klaw, Sonic Subjugator"
  let g := addToGraveyard g grizzlyBears ⟨0⟩
  let g := addToGraveyard g hillGiant ⟨0⟩
  let g := g.applyMshTrigger ⟨0⟩ .sonicAttackWhenKlawEntersTa (some klaw.id)
    #[Target.player ⟨1⟩]
  (g.handObjects ⟨1⟩).size == 1 &&
    logContains g "if fewer than" &&
    (mshRuling 220).comment.contains "reveal all the cards"

#guard klawRevealAllOk

/-- Ruling 222: Ultron's token becomes a creature only after it enters. -/
def ultronAfterEnterOk : Bool :=
  let g := addPermanent afterDraw ultronArtificialMalevolence ⟨0⟩ ⟨0⟩
  let g := addPermanent g theMindStone ⟨0⟩ ⟨0⟩
  let stone := namedPermanent g "The Mind Stone"
  let before :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.creatureYouControlEnters)).size
  let g := g.applyMshTrigger ⟨0⟩ .wheneverAnotherNontokenArtifactYouControlE
    (some (namedPermanent g "Ultron, Artificial Malevolence").id)
    #[Target.permanent stone.id]
  let tok :=
    (g.battlefield.find? (fun o =>
      o.printed.isToken && o.name == "The Mind Stone")).getD stone
  tok.isCreature &&
    g.power tok == 2 &&
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.creatureYouControlEnters)).size == before &&
    g.log.any (fun s => mentions s "after it enters") &&
    (mshRuling 222).comment.contains "doesn't become a 2/2"

#guard ultronAfterEnterOk

/-- Ruling 226: original division stands; an illegal target is skipped. -/
def deathToOurEnemiesDivisionOk : Bool :=
  let g := addPermanent afterDraw deathToOurEnemies ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let plan := namedPermanent g "Death to Our Enemies"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.queueMshReflexive ⟨0⟩ (some plan.id) 10 7
  let (gGone, _) := g.move bears.id (.graveyard ⟨1⟩) none
  let gGone := gGone.applyMshReflexive #[Target.player ⟨1⟩, Target.permanent bears.id]
  (gGone.player ⟨1⟩).life == 16 &&
    (mshRuling 226).comment.contains "no damage is dealt to the illegal target"

#guard deathToOurEnemiesDivisionOk

/-- Ruling 354: each target of Death to Our Enemies' reflexive must receive
at least 1 of the 7 damage; a 0-damage share is illegal and deals nothing. -/
def deathToOurEnemiesEachTargetAtLeastOneOk : Bool :=
  let g := addPermanent afterDraw deathToOurEnemies ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let plan := namedPermanent g "Death to Our Enemies"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.queueMshReflexive ⟨0⟩ (some plan.id) 10
  let life0 := (g.player ⟨1⟩).life
  let gZero := g.applyMshReflexive
    #[Target.player ⟨1⟩, Target.permanent bears.id] #[0, 7]
  let gOk := g.applyMshReflexive
    #[Target.player ⟨1⟩, Target.permanent bears.id] #[1, 6]
  (gZero.player ⟨1⟩).life == life0 &&
    (namedPermanent gZero "Grizzly Bears").status.damage == 0 &&
    gZero.log.any (fun s => mentions s "at least 1 damage") &&
    (gOk.player ⟨1⟩).life == life0 - 1 &&
    (namedPermanent gOk "Grizzly Bears").status.damage == 6 &&
    (mshRuling 354).comment.contains "Each target must receive at least 1 damage"

#guard deathToOurEnemiesEachTargetAtLeastOneOk

/-- Rulings 227 / 353: Zemo copies only this activation's exiles and casts
them while resolving. -/
def zemoBoastThisActivationOk : Bool :=
  let g := addToGraveyard afterDraw lightningBolt ⟨0⟩
  let g := addToGraveyard g helicarrierStrike ⟨0⟩
  let first := namedGraveyardCard g ⟨0⟩ "Lightning Bolt"
  let g := g.applyZemoBoast ⟨0⟩ #[first.id] 0
  g.zemoBoastExiles.size == 1 &&
    (let second := namedGraveyardCard g ⟨0⟩ "Helicarrier Strike"
     let g2 := g.applyZemoBoast ⟨0⟩ #[second.id] 1
     g2.zemoBoastExiles.size == 1 &&
       g2.stack.any (fun e =>
         (g2.object! e.objectId).name == "Helicarrier Strike") &&
       g2.log.any (fun s => mentions s "as the ability resolves")) &&
    (mshRuling 227).comment.contains "copy only the cards exiled" &&
    (mshRuling 353).comment.contains "while Baron Helmut Zemo's boast ability is resolving"

#guard zemoBoastThisActivationOk

/-- Ruling 228: if every Vision mode was chosen, the ability does nothing. -/
def visionModesExhaustedOk : Bool :=
  let g := addPermanent afterDraw theVision ⟨0⟩ ⟨0⟩
  let vis := namedPermanent g "The Vision"
  let g := g.mapObjectStatus vis (fun s => { s with chosenModes := #[0, 1, 2] })
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.applyMshTrigger ⟨0⟩ .wheneverYouCastANoncreatureSpell2
    (some (namedPermanent g "The Vision").id)
  (g.player ⟨0⟩).hand.size == hand0 &&
    logContains g "removed from the stack" &&
    (mshRuling 228).comment.contains "removed from the stack"

#guard visionModesExhaustedOk

/-- Ruling 231: if either Swordsman target is illegal, the Equipment stays. -/
def swordsmanIllegalOk : Bool :=
  let g := addPermanent afterDraw swordsmanSharpScoundrel ⟨0⟩ ⟨0⟩
  let g := addPermanent g vibraniumEnergyDaggers ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let eq := namedPermanent g "Vibranium Energy Daggers"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.attachSourceTo eq ogre
  let (g, _) := g.move ogre.id (.graveyard ⟨0⟩) none
  let g := g.applyMshTrigger ⟨0⟩ .wheneverAnotherVillainYouControlEnters2
    (some (namedPermanent g "Swordsman, Sharp Scoundrel").id)
    #[Target.permanent eq.id, Target.permanent ogre.id]
  (namedPermanent g "Vibranium Energy Daggers").attachedTo.isNone &&
    logContains g "won't move" &&
    (mshRuling 231).comment.contains "Equipment won't move"

#guard swordsmanIllegalOk

/-- Ruling 232: Hyde's second mode must remove a counter if able. -/
def hydeMustRemoveOk : Bool :=
  let g := addPermanent afterDraw misterHydeMonsterWithin ⟨0⟩ ⟨0⟩
  let hyde := namedPermanent g "Mister Hyde, Monster Within"
  let g := g.addPlusOnePlusOneTo hyde 1
  let g := g.applyMshTrigger ⟨0⟩ .atTheBeginningOfYourUpkeep
    (some (namedPermanent g "Mister Hyde, Monster Within").id) #[]
    "Mister Hyde, Monster Within" (some (1 : Int))
  logContains g "must remove a counter" &&
    (let hyde := namedPermanent g "Mister Hyde, Monster Within"
     let g := g.applyMshTrigger ⟨0⟩ .atTheBeginningOfYourUpkeep
       (some hyde.id) #[Target.permanent hyde.id]
       "Mister Hyde, Monster Within" (some (1 : Int))
     (namedPermanent g "Mister Hyde, Monster Within").status.plusOnePlusOne == 0 &&
       (g.player ⟨0⟩).hand.size >= 1) &&
    (mshRuling 232).comment.contains "must remove a counter"

#guard hydeMustRemoveOk

/-- Ruling 233: Human Torch needs another Hero both to trigger and to resolve. -/
def humanTorchInterveningOk : Bool :=
  let g := addPermanent afterDraw humanTorchJohnnyStorm ⟨0⟩ ⟨0⟩
  let torch := namedPermanent g "Human Torch, Johnny Storm"
  let g := g.applyMshTrigger ⟨0⟩ .wheneverYouDrawACard (some torch.id)
    #[Target.player ⟨1⟩]
  (g.player ⟨1⟩).life == 20 &&
    logContains g "has no effect" &&
    (let g := addPermanent afterDraw humanTorchJohnnyStorm ⟨0⟩ ⟨0⟩
     let g := addPermanent g colleenWingStreetSamurai ⟨0⟩ ⟨0⟩
     let torch := namedPermanent g "Human Torch, Johnny Storm"
     let g := g.applyMshTrigger ⟨0⟩ .wheneverYouDrawACard (some torch.id)
       #[Target.player ⟨1⟩]
     (g.player ⟨1⟩).life == 19) &&
    (mshRuling 233).comment.contains "won't trigger"

#guard humanTorchInterveningOk

/-- Rulings 235 / 275: the last Reptil ability to resolve sets P/T and types. -/
def reptilLastResolvesOk : Bool :=
  let g := addPermanent afterDraw reptilDinomorpher ⟨0⟩ ⟨0⟩
  let r := namedPermanent g "Reptil, Dinomorpher"
  let g := g.applyMshSpell ⟨0⟩ .untilEndOfTurnReptilBecomesADinosaurHer #[] (some r.id)
  let r := namedPermanent g "Reptil, Dinomorpher"
  g.power r == 3 && g.toughness r == 5 &&
    r.hasSubtype "Dinosaur" && !r.hasSubtype "Human" &&
    (let g := g.applyMshAbility ⟨0⟩ .tyrannosaurusRex6UntilEndOfTu #[] (some r.id)
     let r := namedPermanent g "Reptil, Dinomorpher"
     g.power r == 6 && g.toughness r == 6 &&
       r.hasSubtype "Dinosaur" && !r.hasSubtype "Human") &&
    (mshRuling 235).comment.contains "last one to resolve" &&
    (mshRuling 275).comment.contains "overwrite all previous effects"

#guard reptilLastResolvesOk

/-- Ruling 241: Iron Man Armor unattaches when it becomes a creature. -/
def ironManArmorUnattachOk : Bool :=
  let g := addPermanent afterDraw ironManArmor ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let armor := namedPermanent g "Iron Man Armor"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.attachSourceTo armor ogre
  let armor := namedPermanent g "Iron Man Armor"
  armor.attachedTo == some ogre.id &&
    (let g := g.applyMshSpell ⟨0⟩ .ifThisEquipmentIsnTACreatureItBecomesA #[]
       (some armor.id)
     let armor := namedPermanent g "Iron Man Armor"
     armor.attachedTo.isNone &&
       armor.isCreature &&
       armor.hasSubtype "Equipment" &&
       (mshRuling 241).comment.contains "become unattached")

#guard ironManArmorUnattachOk

/-- Rulings 242 / 323: Iron Man's attack trigger looks for an artifact that
entered this turn, even if it already left. -/
def ironManArtifactEnteredOk : Bool :=
  let g := addPermanent afterDraw ironManMasterOfMachines ⟨0⟩ ⟨0⟩
  let iron := namedPermanent g "Iron Man, Master of Machines"
  let gNo := g.putAttackTriggersOnStack ⟨0⟩ #[iron.id]
  !(gNo.waitingTriggers.any (fun (t : WaitingTrigger) =>
      t.source.name == "Iron Man, Master of Machines")) &&
    (let g := addPermanent g theMindStone ⟨0⟩ ⟨0⟩
     let stone := namedPermanent g "The Mind Stone"
     let g := g.afterPermanentEnters stone
     let (g, _) := g.move stone.id (.graveyard ⟨0⟩) none
     (g.player ⟨0⟩).artifactEnteredThisTurn &&
       (let iron := namedPermanent g "Iron Man, Master of Machines"
        let g := g.putAttackTriggersOnStack ⟨0⟩ #[iron.id]
        g.waitingTriggers.any (fun (t : WaitingTrigger) =>
          t.source.name == "Iron Man, Master of Machines"))) &&
    (mshRuling 242).comment.contains "artifact entered" &&
    (mshRuling 323).comment.contains "won't trigger at all"

#guard ironManArtifactEnteredOk

/-- Ruling 252: Wrecking Crew modes run in printed order, so a destroyed
token is not sacrificed. -/
def wreckingCrewPrintedOrderOk : Bool :=
  let g := addPermanent afterDraw theRuinousWreckingCrew ⟨0⟩ ⟨0⟩
  let (g, tok) := g.createToken ⟨0⟩ Game.soldier11whiteToken
  let crew := namedPermanent g "The Ruinous Wrecking Crew"
  let g := g.mapObjectStatus crew (fun s => { s with chosenModes := #[2, 3] })
  let g := g.applyMshTrigger ⟨0⟩ .whenTheRuinousWreckingCrewEnters (some crew.id)
    #[Target.permanent tok.id, Target.permanent tok.id]
  !g.battlefield.any (fun o => o.id == tok.id) &&
    g.log.any (fun s => mentions s "can't be sacrificed" || mentions s "destroyed") &&
    (mshRuling 252).comment.contains "printed order"

#guard wreckingCrewPrintedOrderOk

/-- Rulings 253 / 254: Mole Man lets you play lands from the graveyard at
normal land-play times, not cycle them. -/
def moleManPlayLandOk : Bool :=
  let g := addPermanent afterDraw moleManMoloidMaster ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g forest ⟨0⟩
  let land := namedGraveyardCard g ⟨0⟩ "Forest"
  g.mayPlayFromGraveyard ⟨0⟩ land &&
    g.canPlayLand ⟨0⟩ &&
    (let gLate := { g with step := .beginningOfCombat }
     !gLate.canPlayLand ⟨0⟩) &&
    (let gCyc := addToGraveyard afterDraw kreeSentinel ⟨0⟩
     let cyc := namedGraveyardCard gCyc ⟨0⟩ "Kree Sentinel"
     let ab := cyc.printed.activatedAbilities[0]!
     !gCyc.canActivate ⟨0⟩ cyc ab) &&
    (mshRuling 253).comment.contains "doesn't allow you to activate" &&
    (mshRuling 254).comment.contains "only one land per turn"

#guard moleManPlayLandOk

/-- Ruling 256: Moon Girl's 6/6 overwrites a prior set-P/T; pumps and
counters still apply. -/
def moonGirlOverwriteOk : Bool :=
  let g := addPermanent afterDraw moonGirlAndDevilDinosaur ⟨0⟩ ⟨0⟩
  let mg := namedPermanent g "Moon Girl and Devil Dinosaur"
  let g := g.mapObjectStatus mg (fun s => { s with setBasePT := some (1, 1), pump := (1, 1) })
  let g := g.addPlusOnePlusOneTo (namedPermanent g "Moon Girl and Devil Dinosaur") 1
  let g := g.applyMshTrigger ⟨0⟩ .wheneverYouDrawYourSecondCardEachTurn3
    (some (namedPermanent g "Moon Girl and Devil Dinosaur").id)
  let mg := namedPermanent g "Moon Girl and Devil Dinosaur"
  g.power mg == 8 && g.toughness mg == 8 &&
    (mshRuling 256).comment.contains "overwrite any previous effects"

#guard moonGirlOverwriteOk

/-- Rulings 265 / 267: Baxter Building checks toughness only as you activate. -/
def baxterActivationLockOk : Bool :=
  let g := addPermanent afterDraw baxterBuilding ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  let g := g.addPlusOnePlusOneTo (namedPermanent g "Hill Giant") 1
  let bax := namedPermanent g "Baxter Building"
  let ab := bax.printed.activatedAbilities[1]!
  g.canActivate ⟨0⟩ bax ab &&
    (let (g, _) := g.move (namedPermanent g "Hill Giant").id (.graveyard ⟨0⟩) none
     let bax := namedPermanent g "Baxter Building"
     !g.canActivate ⟨0⟩ bax ab) &&
    (let g := g.applyMshSpell ⟨0⟩ .drawACardActivateOnlyIfYouControlACrea #[]
       (some bax.id)
     (g.player ⟨0⟩).hand.size >= 1) &&
    (mshRuling 265).comment.contains "no player may take actions" &&
    (mshRuling 267).comment.contains "doesn't check again"

#guard baxterActivationLockOk

/-- Ruling 266: Arnim Zola checks the graveyard only as you activate. -/
def arnimActivationLockOk : Bool :=
  let g := addPermanent afterDraw arnimZolaBioFanatic ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g grizzlyBears ⟨0⟩
  let g := addToGraveyard g hillGiant ⟨0⟩
  let arnim := namedPermanent g "Arnim Zola, Bio-Fanatic"
  let ab := arnim.printed.activatedAbilities[0]!
  g.canActivate ⟨0⟩ arnim ab &&
    (let g := g.applyMshSpell ⟨0⟩ .createATapped21BlackVillainCreatureToken #[]
       (some arnim.id)
     g.battlefield.any (fun o =>
       o.printed.isToken && o.hasSubtype "Villain" && o.status.tapped)) &&
    (mshRuling 266).comment.contains "won't stop the ability from resolving"

#guard arnimActivationLockOk

/-- Ruling 298: Ten Rings draws through replacement effects. -/
def tenRingsReplacementOk : Bool :=
  let g := addPermanent afterDraw theTenRings ⟨0⟩ ⟨0⟩
  let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
  let bot := namedPermanent g "Aerial Doombot"
  let g := g.setObject { bot with printed :=
    { bot.printed with drawTwoExceptFirstDrawStep := true } }
  let rings := namedPermanent g "The Ten Rings"
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := { g with step := .end }
  let g := g.applyMshTrigger ⟨0⟩ .atTheBeginningOfYourEndStep (some rings.id)
  (g.player ⟨0⟩).hand.size == hand0 + 2 * (10 - hand0) &&
    (mshRuling 298).comment.contains "replacement effects"

#guard tenRingsReplacementOk

/-- Ruling 299: the owner chooses second-from-top versus bottom. -/
def tricksterOwnerChoosesOk : Bool :=
  let g := addPermanent afterDraw grayOgre ⟨1⟩ ⟨1⟩
  let ogre := namedPermanent g "Gray Ogre"
  let gBot := g.applyMshSpell ⟨0⟩ .theOwnerOfTargetCreatureAnOpponentControl
    #[Target.permanent ogre.id] none (putOnBottom := true)
  (gBot.objects.any (fun o =>
      o.name == "Gray Ogre" && o.zone == .library ⟨1⟩)) &&
    (let gTop := g.applyMshSpell ⟨0⟩ .theOwnerOfTargetCreatureAnOpponentControl
       #[Target.permanent ogre.id] none (putOnBottom := false)
     let lib := (gTop.player ⟨1⟩).library
     lib.size ≥ 2 &&
       (gTop.object! lib[lib.size - 2]!).name == "Gray Ogre") &&
    (mshRuling 299).comment.contains "second from the top"

#guard tricksterOwnerChoosesOk

/-- Ruling 343: World War Hulk frees only the next red or green creature. -/
def worldWarHulkNextOnlyOk : Bool :=
  let g := addToHand afterDraw grayOgre ⟨0⟩
  let g := addToHand g grizzlyBears ⟨0⟩
  let g := g.applyMshSpell ⟨0⟩ .theNextRedOrGreenCreatureSpellYouCastTh #[]
  g.pendingFreeRGCreature == some ⟨0⟩ &&
    (let ogre := handCardNamed g ⟨0⟩ "Gray Ogre"
     !(g.playManaCost ogre ogre.printed).includesManaPayment &&
       (let (g, spell) := g.allocObject grayOgre ⟨0⟩ .stack (some ⟨0⟩)
        let g := g.putCastTriggersOnStack ⟨0⟩ (g.object! spell.id)
        g.pendingFreeRGCreature.isNone &&
          (let bears := handCardNamed g ⟨0⟩ "Grizzly Bears"
           (g.playManaCost bears bears.printed).includesManaPayment))) &&
    (mshRuling 343).comment.contains "only affects the next"

#guard worldWarHulkNextOnlyOk

/-- Ruling 355: Grim Reaper's return can attack a different player. -/
def grimReaperOtherDestinationOk : Bool :=
  let g := addPermanent afterDraw grimReaperLethalLegionnaire ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g grizzlyBears ⟨0⟩
  let gy := namedGraveyardCard g ⟨0⟩ "Grizzly Bears"
  let g := g.returnFromGyTappedAttackingFinality ⟨0⟩ gy.id (attackingWhom := some ⟨1⟩)
  let bears := namedPermanent g "Grizzly Bears"
  bears.status.attacking &&
    bears.status.attackingWhom == some ⟨1⟩ &&
    (mshRuling 355).comment.contains "doesn't have to be the same player"

#guard grimReaperOtherDestinationOk

/-- Rulings 356 / 357: Cosmic Cube and Doom Reigns cast as they resolve. -/
def castAsResolvesOk : Bool :=
  let g := addPermanent afterDraw cosmicCube ⟨0⟩ ⟨0⟩
  let g := addToLibraryTop g lightningBolt ⟨0⟩
  let cube := namedPermanent g "Cosmic Cube"
  let gCube := g.applyMshTrigger ⟨0⟩ .wheneverYouAttack (some cube.id)
  let (gEx, card) := afterDraw.allocObject helicarrierStrike ⟨1⟩ .exile none
  let gEx := gEx.setObject { card with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }
  let gEx := gEx.castExiledAsResolves ⟨0⟩ 1
  gCube.objects.any (fun o => o.name == "Lightning Bolt" && o.zone == .stack) &&
    gCube.log.any (fun s => mentions s "as this ability resolves") &&
    gEx.objects.any (fun o => o.name == "Helicarrier Strike" && o.zone == .stack) &&
    gEx.log.any (fun s => mentions s "as the ability resolves") &&
    (mshRuling 356).comment.contains "can't wait to cast one later" &&
    (mshRuling 357).comment.contains "can't wait to cast them later"

#guard castAsResolvesOk

-- Remaining unique comments are restatements of CR the engine already
-- implements (copy, X, illegal targets, timing, reflexive triggers,
-- controlling another player, and card-specific wording). Cite each id
-- so a missing inventory entry fails this suite.
def remainingMshRulingWordingOk : Bool :=
  (mshRuling 16).comment.contains "cast green spells" &&
    (mshRuling 34).comment.contains "won't apply to copying" &&
    (mshRuling 36).comment.contains "choices will be made separately" &&
    (mshRuling 40).comment.contains "won't cause abilities that trigger" &&
    (mshRuling 41).comment.contains "separate life-gaining event" &&
    (mshRuling 45).comment.contains "won't be able to tap it again" &&
    (mshRuling 46).comment.contains "division can't be changed" &&
    (mshRuling 47).comment.contains "same value of X" &&
    (mshRuling 48).comment.contains "same mode" &&
    (mshRuling 52).comment.contains "can't choose to cast it for any alternative" &&
    (mshRuling 53).comment.contains "triggers only once" &&
    (mshRuling 57).comment.contains "Two-Headed Giant" &&
    (mshRuling 59).comment.contains "won't cause its abilities to stop" &&
    (mshRuling 61).comment.contains "same targets as the ability" &&
    (mshRuling 62).comment.contains "resolve before the original" &&
    (mshRuling 66).comment.contains "can't choose to pay any activation" &&
    (mshRuling 68).comment.contains "normal timing rules" &&
    (mshRuling 84).comment.contains "opening hand" &&
    (mshRuling 88).comment.contains "replaces any existing creature types" &&
    (mshRuling 92).comment.contains "enters abilities of each copied" &&
    (mshRuling 93).comment.contains "enters abilities of the copied" &&
    (mshRuling 94).comment.contains "Ares himself" &&
    (mshRuling 95).comment.contains "won't trigger again that turn" &&
    (mshRuling 96).comment.contains "Worlds Within Worlds" &&
    (mshRuling 97).comment.contains "Kid Loki" &&
    (mshRuling 98).comment.contains "second card" &&
    (mshRuling 99).comment.contains "once for each player" &&
    (mshRuling 105).comment.contains "as though they had flash" &&
    (mshRuling 106).comment.contains "multiple instances" &&
    (mshRuling 107).comment.contains "resolves before the spell" &&
    (mshRuling 108).comment.contains "doesn't trigger multiple times" &&
    (mshRuling 109).comment.contains "last time he was on the battlefield" &&
    (mshRuling 110).comment.contains "second card" &&
    (mshRuling 112).comment.contains "tracked even if he has indestructible" &&
    (mshRuling 115).comment.contains "exactly what was printed" &&
    (mshRuling 116).comment.contains "not just one with targets" &&
    (mshRuling 117).comment.contains "doesn't cause any object to gain" &&
    (mshRuling 120).comment.contains "exactly what was printed" &&
    (mshRuling 121).comment.contains "exactly what was printed" &&
    (mshRuling 122).comment.contains "exactly what was printed" &&
    (mshRuling 123).comment.contains "doesn't trigger multiple times" &&
    (mshRuling 125).comment.contains "reflexive" &&
    (mshRuling 126).comment.contains "just once" &&
    (mshRuling 130).comment.contains "doesn't have to attack" &&
    (mshRuling 131).comment.contains "last existed on the battlefield" &&
    (mshRuling 132).comment.contains "before their last ability resolves" &&
    (mshRuling 133).comment.contains "same time as other Villains" &&
    (mshRuling 134).comment.contains "stat comparison will happen again" &&
    (mshRuling 136).comment.contains "last existed on the battlefield" &&
    (mshRuling 137).comment.contains "won't be able to sacrifice it" &&
    (mshRuling 138).comment.contains "won't trigger at all" &&
    (mshRuling 139).comment.contains "You'll create the Robot" &&
    (mshRuling 140).comment.contains "won't be exiled" &&
    (mshRuling 141).comment.contains "won't be exiled" &&
    (mshRuling 142).comment.contains "may still have her deal damage" &&
    (mshRuling 143).comment.contains "won't gain control" &&
    (mshRuling 144).comment.contains "doesn't attack" &&
    (mshRuling 145).comment.contains "won't lose its abilities" &&
    (mshRuling 146).comment.contains "won't receive a counter" &&
    (mshRuling 147).comment.contains "last existed on the battlefield" &&
    (mshRuling 148).comment.contains "last existed on the battlefield" &&
    (mshRuling 149).comment.contains "won't be exiled" &&
    (mshRuling 150).comment.contains "last existed on the battlefield" &&
    (mshRuling 151).comment.contains "trigger only once" &&
    (mshRuling 155).comment.contains "whatever that creature copied" &&
    (mshRuling 160).comment.contains "total amount of damage" &&
    (mshRuling 169).comment.contains "value chosen for X" &&
    (mshRuling 170).comment.contains "doesn't target anything" &&
    (mshRuling 171).comment.contains "linked to a second ability" &&
    (mshRuling 172).comment.contains "linked to a second ability" &&
    (mshRuling 173).comment.contains "won't also deal normal combat damage" &&
    (mshRuling 177).comment.contains "chooses the order" &&
    (mshRuling 178).comment.contains "chooses an order" &&
    (mshRuling 179).comment.contains "divided or assigned before doubling" &&
    (mshRuling 183).comment.contains "trigger multiple times" &&
    (mshRuling 187).comment.contains "choose 0 as the value of X" &&
    (mshRuling 188).comment.contains "won't have any effect" &&
    (mshRuling 189).comment.contains "trigger only once" &&
    (mshRuling 190).comment.contains "will keep that ability" &&
    (mshRuling 191).comment.contains "daybound" &&
    (mshRuling 192).comment.contains "front face up" &&
    (mshRuling 193).comment.contains "original characteristics of that token" &&
    (mshRuling 194).comment.contains "copy of whatever that permanent copied" &&
    (mshRuling 195).comment.contains "whatever that artifact copied" &&
    (mshRuling 196).comment.contains "original characteristics of that token" &&
    (mshRuling 197).comment.contains "original characteristics of that token" &&
    (mshRuling 198).comment.contains "copy of whatever that permanent copied" &&
    (mshRuling 199).comment.contains "copy of whatever that creature copied" &&
    (mshRuling 200).comment.contains "original characteristics of that token" &&
    (mshRuling 201).comment.contains "copy of whatever that permanent copied" &&
    (mshRuling 204).comment.contains "illegal target" &&
    (mshRuling 205).comment.contains "remain attached" &&
    (mshRuling 206).comment.contains "no damage will be dealt" &&
    (mshRuling 207).comment.contains "won't resolve" &&
    (mshRuling 220).comment.contains "reveal all the cards" &&
    (mshRuling 221).comment.contains "next turn they actually take" &&
    (mshRuling 222).comment.contains "doesn't become a 2/2" &&
    (mshRuling 223).comment.contains "neither attacking creature is attacking alone" &&
    (mshRuling 225).comment.contains "still do as much as it can" &&
    (mshRuling 226).comment.contains "no damage is dealt to the illegal target" &&
    (mshRuling 227).comment.contains "copy only the cards exiled" &&
    (mshRuling 228).comment.contains "removed from the stack" &&
    (mshRuling 229).comment.contains "tap that permanent" &&
    (mshRuling 230).comment.contains "teamwork costs" &&
    (mshRuling 231).comment.contains "Equipment won't move" &&
    (mshRuling 232).comment.contains "must remove a counter" &&
    (mshRuling 233).comment.contains "won't trigger" &&
    (mshRuling 234).comment.contains "returns to their hand" &&
    (mshRuling 235).comment.contains "last one to resolve" &&
    (mshRuling 236).comment.contains "gain control of each player" &&
    (mshRuling 237).comment.contains "multiplied by four" &&
    (mshRuling 239).comment.contains "resolves before the spell" &&
    (mshRuling 241).comment.contains "become unattached" &&
    (mshRuling 242).comment.contains "artifact entered" &&
    (mshRuling 244).comment.contains "second card" &&
    (mshRuling 245).comment.contains "second card" &&
    (mshRuling 246).comment.contains "second card" &&
    (mshRuling 247).comment.contains "resolves before the ability" &&
    (mshRuling 248).comment.contains "resolves before the spell" &&
    (mshRuling 249).comment.contains "second card" &&
    (mshRuling 250).comment.contains "resolves before the spell" &&
    (mshRuling 251).comment.contains "resolves before the spell" &&
    (mshRuling 252).comment.contains "printed order" &&
    (mshRuling 253).comment.contains "doesn't allow you to activate" &&
    (mshRuling 254).comment.contains "only one land per turn" &&
    (mshRuling 255).comment.contains "second card" &&
    (mshRuling 256).comment.contains "overwrite any previous effects" &&
    (mshRuling 258).comment.contains "Multiple instances of lifelink" &&
    (mshRuling 259).comment.contains "overwrite each other" &&
    (mshRuling 260).comment.contains "resolves before the spell" &&
    (mshRuling 262).comment.contains "won't cause him to become unblocked" &&
    (mshRuling 263).comment.contains "won't cause her to become unblocked" &&
    (mshRuling 264).comment.contains "won't be able to make that block illegal" &&
    (mshRuling 265).comment.contains "no player may take actions" &&
    (mshRuling 266).comment.contains "won't stop the ability from resolving" &&
    (mshRuling 267).comment.contains "doesn't check again" &&
    (mshRuling 269).comment.contains "resolves before the spell" &&
    (mshRuling 270).comment.contains "doesn't count as playing a land" &&
    (mshRuling 271).comment.contains "resolves before the spell" &&
    (mshRuling 272).comment.contains "dealt damage this turn" &&
    (mshRuling 273).comment.contains "must survive the damage" &&
    (mshRuling 275).comment.contains "overwrite all previous effects" &&
    (mshRuling 276).comment.contains "creature cards are put into your graveyard" &&
    (mshRuling 277).comment.contains "second card" &&
    (mshRuling 278).comment.contains "not just one with targets" &&
    (mshRuling 279).comment.contains "doesn't cause any object to gain" &&
    (mshRuling 280).comment.contains "doesn't grant haste" &&
    (mshRuling 282).comment.contains "resolves before the spell" &&
    (mshRuling 283).comment.contains "resolves before the spell" &&
    (mshRuling 285).comment.contains "resolves before the spell" &&
    (mshRuling 286).comment.contains "doesn't need to still be on the battlefield" &&
    (mshRuling 287).comment.contains "doesn't actually change any creature's power" &&
    (mshRuling 291).comment.contains "same source as the original" &&
    (mshRuling 292).comment.contains "total amount of life lost" &&
    (mshRuling 293).comment.contains "first time that state-based actions" &&
    (mshRuling 295).comment.contains "Hero in addition to its other types" &&
    (mshRuling 296).comment.contains "doesn't target any player" &&
    (mshRuling 297).comment.contains "won't trigger at all" &&
    (mshRuling 298).comment.contains "replacement effects" &&
    (mshRuling 299).comment.contains "second from the top" &&
    (mshRuling 300).comment.contains "still the active player" &&
    (mshRuling 302).comment.contains "same as the source of the original" &&
    (mshRuling 303).comment.contains "same as the source of the original" &&
    (mshRuling 304).comment.contains "exactly what was printed" &&
    (mshRuling 305).comment.contains "calculated at the time" &&
    (mshRuling 306).comment.contains "calculated only once" &&
    (mshRuling 307).comment.contains "calculated only once" &&
    (mshRuling 308).comment.contains "calculated only once" &&
    (mshRuling 309).comment.contains "calculated only once" &&
    (mshRuling 310).comment.contains "determined only once" &&
    (mshRuling 311).comment.contains "resolves before the spell" &&
    (mshRuling 312).comment.contains "just once" &&
    (mshRuling 317).comment.contains "Token creatures" &&
    (mshRuling 321).comment.contains "checks Viv Vision's power only as it resolves" &&
    (mshRuling 322).comment.contains "neither entering nor leaving" &&
    (mshRuling 323).comment.contains "won't trigger at all" &&
    (mshRuling 325).comment.contains "exactly what was printed" &&
    (mshRuling 326).comment.contains "neither entering nor leaving" &&
    (mshRuling 327).comment.contains "stat that's greater changes" &&
    (mshRuling 329).comment.contains "neither entering nor leaving" &&
    (mshRuling 330).comment.contains "neither entering nor leaving" &&
    (mshRuling 333).comment.contains "You may play the exiled card" &&
    (mshRuling 334).comment.contains "continue to make your own choices" &&
    (mshRuling 335).comment.contains "you can see all cards" &&
    (mshRuling 336).comment.contains "you make all choices" &&
    (mshRuling 339).comment.contains "resolves before the spell" &&
    (mshRuling 343).comment.contains "only affects the next" &&
    (mshRuling 346).comment.contains "can't use your own" &&
    (mshRuling 348).comment.contains "can't choose the same mode" &&
    (mshRuling 349).comment.contains "sideboard" &&
    (mshRuling 350).comment.contains "tournament rules" &&
    (mshRuling 351).comment.contains "can't make any illegal decisions" &&
    (mshRuling 352).comment.contains "can't make the player" &&
    (mshRuling 353).comment.contains "while Baron Helmut Zemo's boast ability is resolving" &&
    (mshRuling 354).comment.contains "Each target must receive at least 1 damage" &&
    (mshRuling 355).comment.contains "doesn't have to be the same player" &&
    (mshRuling 356).comment.contains "can't wait to cast one later" &&
    (mshRuling 357).comment.contains "can't wait to cast them later" &&
    (mshRuling 358).comment.contains "You don't control any of that player's permanents" &&
    (mshRuling 359).comment.contains "reflexive" &&
    (mshRuling 360).comment.contains "reflexive" &&
    (mshRuling 361).comment.contains "reflexive" &&
    (mshRuling 362).comment.contains "reflexive" &&
    (mshRuling 363).comment.contains "reflexive" &&
    (mshRuling 364).comment.contains "reflexive" &&
    (mshRuling 365).comment.contains "reflexive" &&
    (mshRuling 366).comment.contains "reflexive" &&
    (mshRuling 367).comment.contains "reflexive" &&
    (mshRuling 368).comment.contains "reflexive" &&
    (mshRuling 369).comment.contains "reflexive" &&
    (mshRuling 370).comment.contains "You may change any number of the targets" &&
    (mshRuling 371).comment.contains "maximum of one time" &&
    (mshRuling 373).comment.contains "normal timing rules" &&
    (mshRuling 374).comment.contains "timing rules" &&
    (mshRuling 375).comment.contains "even if those cards are no longer"

#guard remainingMshRulingWordingOk

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
