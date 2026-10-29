import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# `TriggerResolution.grant`

What is granted is `TriggerGrantWhat`. Who receives it is an `ObjectSelector`.
Equipped attacking creatures gaining double strike, and the controller
gaining protection from everything when the source was cast. Any other
permanent the selector names receives that ability. A card or an unmade
choice receives nothing.
-/

namespace Mtg.Engine.GrantTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) : Game :=
  g.applyTriggeredAbility caster (.onEnterDraw 1) sourceId
    (resolutionOverride := some r)

def obj (g : Game) (name : String) : GameObject :=
  match g.battlefield.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def anyObj (g : Game) (name : String) : GameObject :=
  match g.objects.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def pid (g : Game) (name : String) : ObjectId :=
  (obj g name).id

def attacking (g : Game) (name : String) : Game :=
  let o := obj g name
  g.markAttacking o.id

def attach (g : Game) (equip host : String) : Game :=
  let eq := obj g equip
  g.changeObject eq.id (.attachedTo (some (pid g host)))

def cast (g : Game) (name : String) : Game :=
  let o := anyObj g name
  g.record (GameEvent.proposed g.turnNumber o.id o.owner (.hand o.owner) .normal)

def strikes (g : Game) (name : String) : Bool :=
  g.hasDoubleStrike (obj g name)

def bear : CardDef := creature "Bear" ManaCost.empty #[] 2 2
def cub : CardDef := creature "Cub" ManaCost.empty #[] 1 1
def foe : CardDef := creature "Foe" ManaCost.empty #[] 3 3
def axe : CardDef := artifact "Axe" ManaCost.empty "" (subtypes := #["Equipment"])
def bow : CardDef := artifact "Bow" ManaCost.empty "" (subtypes := #["Equipment"])
def cloak : CardDef := enchantment "Cloak" ManaCost.empty ""
def ring : CardDef := artifact "Ring" ManaCost.empty ""

def doubleStrike : TriggeredAbility.TriggerResolution :=
  .grant .doubleStrike .equippedAttackers

def protection : TriggeredAbility.TriggerResolution :=
  .grant .protectionEverything .youIfCast

def battle : Game :=
  let g := addPermanent afterDraw bear caster caster
  let g := addPermanent g cub caster caster
  let g := addPermanent g foe opp opp
  let g := addPermanent g axe caster caster
  let g := addPermanent g bow opp opp
  let g := addPermanent g cloak caster caster
  attacking (attacking g "Bear") "Foe"

/- Each equipped attacking creature gains double strike. An attachment on
the battlefield is enough: Equipment and an Aura both count, and the
creature may be an opponent's. An equipped creature that is not
attacking stays as it is. With nothing attached, attacking creatures
do too. -/
#guard
  let g0 := attach (attach (attach battle "Axe" "Bear") "Bow" "Foe") "Cloak" "Cub"
  let g := step g0 doubleStrike
  strikes g "Bear" && strikes g "Foe" &&
    !strikes g "Cub" &&
    logContains g "Bear gains double strike until end of turn" &&
    logContains g "Foe gains double strike until end of turn" &&
    !(logContains g "Cub gains")

#guard
  let g := step battle doubleStrike
  !strikes g "Bear" && !strikes g "Foe" && g.log.size == battle.log.size

/- An attacking creature that is attached to something, with nothing
attached to it, does not gain double strike. An attachment that has
left the battlefield does not count. -/
#guard
  let rider : CardDef := creature "Rider" ManaCost.empty #[] 2 2
  let g0 := attacking (addPermanent battle rider caster caster) "Rider"
  let riderObj := obj g0 "Rider"
  let g0 := g0.changeObject riderObj.id (.attachedTo (some (pid g0 "Cub")))
  let g := step g0 doubleStrike
  !strikes g "Rider" && !strikes g "Cub" && !strikes g "Bear"

#guard
  let g0 := attach battle "Axe" "Bear"
  let (g1, _) := g0.move (pid g0 "Axe") (.graveyard caster)
  let g := step g1 doubleStrike
  !strikes g "Bear"

/- Protection from everything is the controller's when the source was
cast, including after that source has left the battlefield. Otherwise
the ability logs that it does nothing. -/
#guard
  let g0 := cast (addPermanent afterDraw ring caster caster) "Ring"
  let g := step g0 protection (some (pid g0 "Ring"))
  g.protectionFromEverything caster &&
    !g.protectionFromEverything opp &&
    logContains g "gains protection from everything"

#guard
  let g0 := insertObject afterDraw ring caster (.graveyard caster)
  let g0 := cast g0 "Ring"
  let g := step g0 protection (some (anyObj g0 "Ring").id)
  g.protectionFromEverything caster &&
    logContains g "gains protection from everything"

#guard
  let g0 := addPermanent afterDraw ring caster caster
  let g := step g0 protection (some (pid g0 "Ring"))
  !g.protectionFromEverything caster &&
    logContains g "It wasn't cast. The ability does nothing."

#guard
  let g := step afterDraw protection
  !g.protectionFromEverything caster &&
    logContains g "It wasn't cast. The ability does nothing."

/- A cast check that names no permanent grants nothing. Protection for
equipped attackers is the controller of those attackers. No Human grants
nothing. -/
#guard
  let g0 := cast (attach (addPermanent battle ring caster caster) "Axe" "Bear") "Ring"
  let crossed := step g0 (.grant .doubleStrike .youIfCast) (some (pid g0 "Ring"))
  !strikes crossed "Bear" && !crossed.protectionFromEverything caster &&
    crossed.log.size == g0.log.size

#guard
  let g0 := cast (attach (addPermanent battle ring caster caster) "Axe" "Bear") "Ring"
  let swapped := step g0 (.grant .protectionEverything .equippedAttackers)
      (some (pid g0 "Ring"))
  !strikes swapped "Bear" && swapped.protectionFromEverything caster &&
    !swapped.protectionFromEverything opp &&
    logContains swapped "Chandra gains protection from everything"

#guard
  let g0 := cast (attach (addPermanent battle ring caster caster) "Axe" "Bear") "Ring"
  let other := step g0 (.grant .doubleStrike .humans) (some (pid g0 "Ring"))
  !strikes other "Bear" && !other.protectionFromEverything caster &&
    other.log.size == g0.log.size

#guard TriggeredAbility.resolution .onAttackEquippedGainDoubleStrike == doubleStrike
#guard TriggeredAbility.resolution .onEnterIfCastProtectionEverything == protection
#guard TriggeredAbility.resolutionPhrase { resolution := doubleStrike } ==
  "each equipped attacking creature gains double strike until end of turn"
#guard TriggeredAbility.resolutionPhrase { resolution := protection } ==
  "if you cast it, you gain protection from everything until your next turn"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .grant .doubleStrike .youIfCast } == "grant"
#guard TriggeredAbility.toNotation .onAttackEquippedGainDoubleStrike ==
  "Whenever Dáin attacks, each equipped attacking creature gains double strike until end of turn."
#guard TriggeredAbility.toNotation .onEnterIfCastProtectionEverything ==
  "When The One Ring enters, if you cast it, you gain protection from everything until your next turn."

end Mtg.Engine.GrantTests
