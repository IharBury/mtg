import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Fixture
import Mtg.Engine.Game
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Enters-or-attacks triggers without `EnterOrAttackLeftover`

Super-Adaptoid puts keyword counters for keywords the target has that it
lacks. Squirrel Girl creates a 1/1 green Squirrel.
-/

namespace Mtg.Engine.EnterOrAttackTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def me : PlayerId := ⟨0⟩

def resolve (g : Game) (ab : TriggeredAbility) (sourceId : Option ObjectId := none)
    (targets : Array Target := #[]) : Game :=
  g.applyTriggeredAbility me ab sourceId targets

def named (g : Game) (name : String) : GameObject :=
  namedPermanent g name

def squirrels (g : Game) : Nat :=
  (g.battlefield.filter (·.name == "Squirrel")).size

/- The shared enters-or-attacks effects resolve as constructors that do not
carry `EnterOrAttackLeftover`. The printed sentence stays the Oracle line. -/
#guard TriggeredAbility.resolution
    (TriggeredAbility.onEnterOrAttack Effect.enterOrAttackCopyKeywords) ==
  .putCounters .missingKeywordsFromTarget .source
#guard TriggeredAbility.resolution
    (TriggeredAbility.onEnterOrAttack Effect.enterOrAttackCreateSquirrel) ==
  .createTokens .squirrel11green (.fixed 1) false

#guard toString (TriggeredAbility.onEnterOrAttack Effect.enterOrAttackCopyKeywords) ==
  Effect.enterOrAttackCopyKeywords.phrase
#guard toString (TriggeredAbility.onEnterOrAttack Effect.enterOrAttackCreateSquirrel) ==
  Effect.enterOrAttackCreateSquirrel.phrase

/- A creature with no extra keywords gives Super-Adaptoid nothing.
Double strike does not also grant first strike. Targeting itself is illegal.
A source that has left puts nothing. -/
def plainBears : Game :=
  let g := addPermanent afterDraw superAdaptoid me me
  let g := addPermanent g grizzlyBears me me
  let adaptoid := named g "Super-Adaptoid"
  let bears := named g "Grizzly Bears"
  resolve g (TriggeredAbility.onEnterOrAttack Effect.enterOrAttackCopyKeywords)
    (some adaptoid.id) #[Target.permanent bears.id]

#guard
  let o := named plainBears "Super-Adaptoid"
  o.status.keywordCounters.haste == 0 && o.status.keywordCounters.flying == 0 &&
    o.status.keywordCounters.doubleStrike == 0 && o.status.keywordCounters.firstStrike == 0

def doubleStrikeOnly : Game :=
  let g := addPermanent afterDraw superAdaptoid me me
  let g := addPermanent g grizzlyBears me me
  let bears := named g "Grizzly Bears"
  let g := g.mapObjectStatus bears (fun s =>
    { s with untilEotKeywords := Keyword.doubleStrike })
  let adaptoid := named g "Super-Adaptoid"
  let bears := named g "Grizzly Bears"
  resolve g (TriggeredAbility.onEnterOrAttack Effect.enterOrAttackCopyKeywords)
    (some adaptoid.id) #[Target.permanent bears.id]

#guard
  let o := named doubleStrikeOnly "Super-Adaptoid"
  o.status.keywordCounters.doubleStrike == 1 &&
    o.status.keywordCounters.firstStrike == 0 &&
    doubleStrikeOnly.hasDoubleStrike o &&
    !o.printed.keywords.doubleStrike

def selfTarget : Game :=
  let g := addPermanent afterDraw superAdaptoid me me
  let adaptoid := named g "Super-Adaptoid"
  resolve g (TriggeredAbility.onEnterOrAttack Effect.enterOrAttackCopyKeywords)
    (some adaptoid.id) #[Target.permanent adaptoid.id]

#guard (named selfTarget "Super-Adaptoid").status.keywordCounters.haste == 0 &&
  logContains selfTarget "no longer legal"

def sourceLeft : Game :=
  let g := addPermanent afterDraw superAdaptoid me me
  let g := addPermanent g grizzlyBears me me
  let adaptoid := named g "Super-Adaptoid"
  let bears := named g "Grizzly Bears"
  let g := g.mapObjectStatus bears (fun s =>
    { s with untilEotKeywords := Keyword.haste })
  let (g, _) := g.move adaptoid.id (.graveyard me) none
  resolve g (TriggeredAbility.onEnterOrAttack Effect.enterOrAttackCopyKeywords)
    (some adaptoid.id) #[Target.permanent bears.id]

#guard logContains sourceLeft "no longer" &&
  !(sourceLeft.objects.any (fun o =>
    o.name == "Super-Adaptoid" && o.status.keywordCounters.haste > 0))

/- Squirrel Girl creates one 1/1 green Squirrel. The token is still created
when the source has left the battlefield. -/
def oneSquirrel : Game :=
  let g := addPermanent afterDraw theUnbeatableSquirrelGirl me me
  resolve g (TriggeredAbility.onEnterOrAttack Effect.enterOrAttackCreateSquirrel)
    (some (named g "The Unbeatable Squirrel Girl").id)

#guard
  let tok := named oneSquirrel "Squirrel"
  squirrels oneSquirrel == 1 && tok.printed.isToken && tok.controller == some me &&
    tok.printed.power == some 1 && tok.printed.toughness == some 1 &&
    tok.subtypes.contains "Squirrel"

def squirrelSourceLeft : Game :=
  let g := addPermanent afterDraw theUnbeatableSquirrelGirl me me
  let src := named g "The Unbeatable Squirrel Girl"
  let (g, _) := g.move src.id (.graveyard me) none
  resolve g (TriggeredAbility.onEnterOrAttack Effect.enterOrAttackCreateSquirrel)
    (some src.id)

#guard squirrels squirrelSourceLeft == 1

end Mtg.Engine.EnterOrAttackTests
