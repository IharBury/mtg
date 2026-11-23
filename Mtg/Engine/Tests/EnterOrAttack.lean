import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Fixture
import Mtg.Engine.Game
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Unified enters-or-attacks triggers

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

/- The enters-or-attacks triggers carry unified `Instruction` bodies and keep their Oracle lines. -/
#guard TriggeredAbility.enterOrAttackCopyKeywords.effect.body == Effect.enterOrAttackCopyKeywords.body
#guard TriggeredAbility.enterOrAttackCreateSquirrel.effect.body == Effect.enterOrAttackCreateSquirrel.body
#guard TriggeredAbility.enterOrAttackCopyKeywords.toNotation.contains "another target creature"
#guard TriggeredAbility.enterOrAttackCreateSquirrel.toNotation.contains "Squirrel"

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
  o.status.counters.count .haste == 0 && o.status.counters.count .flying == 0 &&
    o.status.counters.count .doubleStrike == 0 && o.status.counters.count .firstStrike == 0

def doubleStrikeOnly : Game :=
  let g := addPermanent afterDraw superAdaptoid me me
  let g := addPermanent g grizzlyBears me me
  let bears := named g "Grizzly Bears"
  let g := g.createEffect (.keywordsUntilEot bears.id #[Keyword.doubleStrike])
  let adaptoid := named g "Super-Adaptoid"
  let bears := named g "Grizzly Bears"
  resolve g (TriggeredAbility.onEnterOrAttack Effect.enterOrAttackCopyKeywords)
    (some adaptoid.id) #[Target.permanent bears.id]

#guard
  let o := named doubleStrikeOnly "Super-Adaptoid"
  o.status.counters.count .doubleStrike == 1 &&
    o.status.counters.count .firstStrike == 0 &&
    doubleStrikeOnly.hasDoubleStrike o &&
    !KeywordAbility.hasDoubleStrike o.printed.keywords

def selfTarget : Game :=
  let g := addPermanent afterDraw superAdaptoid me me
  let adaptoid := named g "Super-Adaptoid"
  resolve g (TriggeredAbility.onEnterOrAttack Effect.enterOrAttackCopyKeywords)
    (some adaptoid.id) #[Target.permanent adaptoid.id]

#guard (named selfTarget "Super-Adaptoid").status.counters.count .haste == 0 &&
  logContains selfTarget "no longer legal"

def sourceLeft : Game :=
  let g := addPermanent afterDraw superAdaptoid me me
  let g := addPermanent g grizzlyBears me me
  let adaptoid := named g "Super-Adaptoid"
  let bears := named g "Grizzly Bears"
  let g := g.createEffect (.keywordsUntilEot bears.id #[Keyword.haste])
  let (g, _) := g.move adaptoid.id (.graveyard me) none
  resolve g (TriggeredAbility.onEnterOrAttack Effect.enterOrAttackCopyKeywords)
    (some adaptoid.id) #[Target.permanent bears.id]

#guard logContains sourceLeft "no longer" &&
  !(sourceLeft.objects.any (fun o =>
    o.name == "Super-Adaptoid" && o.status.counters.count .haste > 0))

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
    (oneSquirrel.subtypes tok).contains .squirrel

def squirrelSourceLeft : Game :=
  let g := addPermanent afterDraw theUnbeatableSquirrelGirl me me
  let src := named g "The Unbeatable Squirrel Girl"
  let (g, _) := g.move src.id (.graveyard me) none
  resolve g (TriggeredAbility.onEnterOrAttack Effect.enterOrAttackCreateSquirrel)
    (some src.id)

#guard squirrels squirrelSourceLeft == 1

end Mtg.Engine.EnterOrAttackTests
