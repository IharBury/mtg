import Mtg.Engine.Catalog
import Mtg.Engine.Fixture
import Mtg.Engine.Game
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Unified watch triggers

Each watch trigger carries a unified `Instruction` body and renders its
Oracle sentence.
-/

namespace Mtg.Engine.WatchTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def me : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def resolve (g : Game) (ab : TriggeredAbility) (sourceId : Option ObjectId := none)
    (targets : Array Target := #[]) (lastKnownPower : Option Int := none) : Game :=
  g.applyTriggeredAbility me ab sourceId targets #[] lastKnownPower

def named (g : Game) (name : String) : GameObject :=
  namedPermanent g name

def onWatch (e : Effect) : TriggeredAbility :=
  TriggeredAbility.onWatch e

/- All watch triggers map to their unified `Instruction` bodies and keep their Oracle lines. -/
#guard (onWatch Effect.watchCombatDamageExileUntilNonland).effect.body ==
  Effect.watchCombatDamageExileUntilNonland.body
#guard (onWatch Effect.watchAttacksAloneDrain).effect.body ==
  Effect.watchAttacksAloneDrain.body
#guard (onWatch Effect.watchAttacksAloneFirstStrikeMenace).effect.body ==
  Effect.watchAttacksAloneFirstStrikeMenace.body
#guard (onWatch Effect.watchFirstTapUntap).effect.body ==
  Effect.watchFirstTapUntap.body
#guard (onWatch Effect.watchSheHulkRedirectOnce).effect.body ==
  Effect.watchSheHulkRedirectOnce.body
#guard (onWatch Effect.watchSpeedballTargeted).effect.body ==
  Effect.watchSpeedballTargeted.body
#guard (onWatch Effect.watchAnyPlayerSecondDraw).effect.body ==
  Effect.watchAnyPlayerSecondDraw.body
#guard (onWatch Effect.watchYouTargetDrawOnce).effect.body ==
  Effect.watchYouTargetDrawOnce.body
#guard (onWatch Effect.watchVillainOrArtifactDamage).effect.body ==
  Effect.watchVillainOrArtifactDamage.body
#guard (onWatch Effect.watchVillainConniveOnce).effect.body ==
  Effect.watchVillainConniveOnce.body
#guard (onWatch Effect.watchVillainPlusOneDamageOnce).effect.body ==
  Effect.watchVillainPlusOneDamageOnce.body
#guard (onWatch Effect.watchVillainAttachEquipment).effect.body ==
  Effect.watchVillainAttachEquipment.body
#guard (onWatch Effect.watchVillainPlusOneLifelink).effect.body ==
  Effect.watchVillainPlusOneLifelink.body
#guard (onWatch Effect.watchHulklingCompare).effect.body ==
  Effect.watchHulklingCompare.body
#guard (onWatch Effect.watchJusticeBounce).effect.body ==
  Effect.watchJusticeBounce.body
#guard (onWatch Effect.watchNontokenHeroModal).effect.body ==
  Effect.watchNontokenHeroModal.body
#guard (onWatch Effect.watchUltronCopy).effect.body ==
  Effect.watchUltronCopy.body
#guard (onWatch Effect.watchEnchantedAttachEquipment).effect.body ==
  Effect.watchEnchantedAttachEquipment.body
#guard (onWatch Effect.watchEquippedAttacksAloneUntapScry).effect.body ==
  Effect.watchEquippedAttacksAloneUntapScry.body
#guard (onWatch Effect.watchEquippedAttacksTap).effect.body ==
  Effect.watchEquippedAttacksTap.body
#guard (onWatch Effect.watchEquippedTappedDamage).effect.body ==
  Effect.watchEquippedTappedDamage.body
#guard (onWatch Effect.watchHeroesDamagePlusTwo).effect.body ==
  Effect.watchHeroesDamagePlusTwo.body
#guard (onWatch Effect.watchMerfolkAttackDraw).effect.body ==
  Effect.watchMerfolkAttackDraw.body
#guard (onWatch Effect.watchTokensEnterMayDraw).effect.body ==
  Effect.watchTokensEnterMayDraw.body
#guard (onWatch Effect.watchHawkeyeModes).effect.body ==
  Effect.watchHawkeyeModes.body
#guard (onWatch Effect.watchRedHulk).effect.body ==
  Effect.watchRedHulk.body
#guard (onWatch Effect.watchHulk).effect.body ==
  Effect.watchHulk.body

#guard (toString TriggeredAbility.watchJusticeBounce).contains "returned to its owner's hand"
#guard (toString (onWatch Effect.watchHulk)).contains "additional combat phase"
#guard (toString (onWatch Effect.watchHawkeyeModes)).contains "Choose up to that many"

/- Justice puts a +1/+1 counter on the source. A draw trigger draws one card.
A declined token-enter draw leaves the hand unchanged. A creature attacking
alone gains first strike and menace. -/
def justiceCounter : Game :=
  let g := addPermanent afterDraw grizzlyBears me me
  resolve g TriggeredAbility.watchJusticeBounce (some (named g "Grizzly Bears").id)

#guard (named justiceCounter "Grizzly Bears").status.plusOnePlusOne == 1

def merfolkDraw : Game :=
  resolve afterDraw (onWatch Effect.watchMerfolkAttackDraw) none

#guard (merfolkDraw.player me).hand.size == (afterDraw.player me).hand.size + 1

def declinedTokenDraw : Game :=
  mustApply (resolve afterDraw (onWatch Effect.watchTokensEnterMayDraw) none) me .decline

#guard (declinedTokenDraw.player me).hand.size == (afterDraw.player me).hand.size &&
  logContains declinedTokenDraw "declines"

def aloneKeywords : Game :=
  let g := addPermanent afterDraw grizzlyBears me me
  let bears := named g "Grizzly Bears"
  let g := g.markAttacking bears.id (some (.player opp))
  resolve g (onWatch Effect.watchAttacksAloneFirstStrikeMenace)
    (some (named g "Grizzly Bears").id)

#guard
  let o := named aloneKeywords "Grizzly Bears"
  aloneKeywords.hasFirstStrike o && aloneKeywords.hasMenace o

end Mtg.Engine.WatchTests
