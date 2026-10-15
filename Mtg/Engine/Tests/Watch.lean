import Mtg.Engine.Catalog
import Mtg.Engine.Fixture
import Mtg.Engine.Game
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Watch triggers without `WatchLeftover`

Each shared watch effect resolves as a `TriggerResolution` that does not
carry `WatchLeftover`. The printed sentence stays the Oracle line.
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

/- The shared watch effects resolve as constructors that do not carry
`WatchLeftover`. -/
#guard TriggeredAbility.resolution (onWatch Effect.watchCombatDamageExileUntilNonland) ==
  .revealLibrary .untilNonland
    (.may (.putCounters (.ofKind .plusOnePlusOne) .source)
      (.exile .top .forLater .anyManaThisTurn) .ifYouDont)
    .announced
#guard TriggeredAbility.resolution (onWatch Effect.watchAttacksAloneDrain) ==
  .sequence [.loseLife 1 (who := .targetOpponent), .gainLife 1]
#guard TriggeredAbility.resolution (onWatch Effect.watchAttacksAloneFirstStrikeMenace) ==
  .grant (.keywords (Keywords.merge Keyword.firstStrike Keyword.menace)) .attackingAlone
#guard TriggeredAbility.resolution (onWatch Effect.watchFirstTapUntap) ==
  .untap .firstThisTurn
#guard TriggeredAbility.resolution (onWatch Effect.watchSheHulkRedirectOnce) ==
  .may (.dealDamage .lastKnownPower .target) (.sequence []) .ifYouDo
#guard TriggeredAbility.resolution (onWatch Effect.watchSpeedballTargeted) ==
  .sequence [.pump (.fixed 2) (.fixed 2) .source, .may .retargetCause (.sequence []) .ifYouDo]
#guard TriggeredAbility.resolution (onWatch Effect.watchAnyPlayerSecondDraw) == .draw (.fixed 1)
#guard TriggeredAbility.resolution (onWatch Effect.watchYouTargetDrawOnce) == .draw (.fixed 1)
#guard TriggeredAbility.resolution (onWatch Effect.watchVillainOrArtifactDamage) ==
  .dealDamage (.fixed 1) .targetOpponent
#guard TriggeredAbility.resolution (onWatch Effect.watchVillainConniveOnce) ==
  .connive .enteringVillain
#guard TriggeredAbility.resolution (onWatch Effect.watchVillainPlusOneDamageOnce) ==
  .sequence [
    .putCounters (.ofKind .plusOnePlusOne) .sourceIfPresent,
    .dealDamage (.fixed 2) .eachOpponent]
#guard TriggeredAbility.resolution (onWatch Effect.watchVillainAttachEquipment) ==
  .attach .announcedEquipment .announcedCreature
#guard TriggeredAbility.resolution (onWatch Effect.watchVillainPlusOneLifelink) ==
  .sequence [.pump (.fixed 1) (.fixed 0) .source, .grant (.keywords Keyword.lifelink) .source]
#guard TriggeredAbility.resolution (onWatch Effect.watchHulklingCompare) ==
  .«if» .causeGreaterPowerOrToughness (.putCounters (.ofKind .plusOnePlusOne) .source)
#guard TriggeredAbility.resolution (onWatch Effect.watchJusticeBounce) ==
  .putCounters (.ofKind .plusOnePlusOne) .source
#guard TriggeredAbility.resolution (onWatch Effect.watchNontokenHeroModal) ==
  .chooseModes
    [.createTokens .soldier11white 1 false, .pump (.fixed 1) (.fixed 1) .creaturesYouControl]
    .fromLastKnown
#guard TriggeredAbility.resolution (onWatch Effect.watchUltronCopy) ==
  .may (.pay #[.generic 2]) (.becomeCopy .cause) .ifYouDo
#guard TriggeredAbility.resolution (onWatch Effect.watchEnchantedAttachEquipment) ==
  .attach .eachTargetEquipment .enchantedCreature
#guard TriggeredAbility.resolution (onWatch Effect.watchEquippedAttacksAloneUntapScry) ==
  .sequence [.untap .equipped, .scry (.fixed 1)]
#guard TriggeredAbility.resolution (onWatch Effect.watchEquippedAttacksTap) == .tap .target
#guard TriggeredAbility.resolution (onWatch Effect.watchEquippedTappedDamage) ==
  .dealDamage (.fixed 1) .eachOpponent .fromEquipped
#guard TriggeredAbility.resolution (onWatch Effect.watchHeroesDamagePlusTwo) ==
  .putCounters (.ofKind .plusOnePlusOne 2) .source
#guard TriggeredAbility.resolution (onWatch Effect.watchMerfolkAttackDraw) == .draw (.fixed 1)
#guard TriggeredAbility.resolution (onWatch Effect.watchTokensEnterMayDraw) ==
  .may (.draw (.fixed 1)) (.sequence []) .ifYouDo
#guard TriggeredAbility.resolution (onWatch Effect.watchHawkeyeModes) ==
  .may (.pay #[.generic 1]) (.queueReflexive (.modeled 2 3)) .ifYouDo
#guard TriggeredAbility.resolution (onWatch Effect.watchRedHulk) ==
  .sequence [
    .putCounters (.ofKind .plusOnePlusOne) .source,
    .queueReflexive (.countersOnSource 8)]
#guard TriggeredAbility.resolution (onWatch Effect.watchHulk) ==
  .sequence [
    .putCounters (.ofKind .plusOnePlusOne) .source,
    .«if» .sourceAttacking (.untap .source),
    .«if» .enrageGrantsCombat .additionalCombatPhase]

#guard toString (onWatch Effect.watchJusticeBounce) ==
  TriggeredAbility.watchSentence .justiceBounce
#guard toString (onWatch Effect.watchHulk) ==
  TriggeredAbility.watchSentence .hulk
#guard toString (onWatch Effect.watchHawkeyeModes) ==
  TriggeredAbility.watchSentence .hawkeyeModes
#guard Effect.watchHulk.resolution == Resolution.trigger (.watch .hulk)

/- Justice puts a +1/+1 counter on the source. A draw trigger draws one card.
A declined token-enter draw leaves the hand unchanged. A creature attacking
alone gains first strike and menace. -/
def justiceCounter : Game :=
  let g := addPermanent afterDraw grizzlyBears me me
  resolve g (onWatch Effect.watchJusticeBounce) (some (named g "Grizzly Bears").id)

#guard (named justiceCounter "Grizzly Bears").status.plusOnePlusOne == 1

def merfolkDraw : Game :=
  resolve afterDraw (onWatch Effect.watchMerfolkAttackDraw) none

#guard (merfolkDraw.player me).hand.size == (afterDraw.player me).hand.size + 1

def declinedTokenDraw : Game :=
  resolve afterDraw (onWatch Effect.watchTokensEnterMayDraw) none #[] (some 0)

#guard (declinedTokenDraw.player me).hand.size == (afterDraw.player me).hand.size &&
  logContains declinedTokenDraw "The optional draw was declined"

def aloneKeywords : Game :=
  let g := addPermanent afterDraw grizzlyBears me me
  let bears := named g "Grizzly Bears"
  let g := g.mapObjectStatus bears (fun s =>
    { s with attacking := true, attackingWhom := some opp })
  resolve g (onWatch Effect.watchAttacksAloneFirstStrikeMenace)
    (some (named g "Grizzly Bears").id)

#guard
  let o := named aloneKeywords "Grizzly Bears"
  aloneKeywords.hasFirstStrike o && aloneKeywords.hasMenace o

end Mtg.Engine.WatchTests
