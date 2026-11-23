import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# Unified grant effects (keywords and player protection)

Equipped attacking creatures gaining double strike, and the controller gaining
protection from everything when the source was cast.
-/

namespace Mtg.Engine.GrantTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def step (g : Game) (ab : TriggeredAbility)
    (sourceId : Option ObjectId := none) : Game :=
  g.applyTriggeredAbility caster ab sourceId

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
  g.record (GameEvent.attached g.turnNumber (g.snapshot eq) (pid g host) (cause := .gameRule .staticAbility))

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

def battle : Game :=
  let g := addPermanent afterDraw bear caster caster
  let g := addPermanent g cub caster caster
  let g := addPermanent g foe opp opp
  let g := addPermanent g axe caster caster
  let g := addPermanent g bow opp opp
  let g := addPermanent g cloak caster caster
  attacking (attacking g "Bear") "Foe"

/- Each equipped attacking creature gains double strike. An equipped creature
that is not attacking stays as it is. With nothing attached, attacking
creatures do too. -/
#guard
  let g0 := attach (attach (attach battle "Axe" "Bear") "Bow" "Foe") "Cloak" "Cub"
  let g := step g0 .onAttackEquippedGainDoubleStrike
  strikes g "Bear" && strikes g "Foe" && !strikes g "Cub"

#guard
  let g := step battle .onAttackEquippedGainDoubleStrike
  !strikes g "Bear" && !strikes g "Foe" && g.log.size == battle.log.size

/- An attacking creature that is attached to something, with nothing
attached to it, does not gain double strike. An attachment that has
left the battlefield does not count. -/
#guard
  let rider : CardDef := creature "Rider" ManaCost.empty #[] 2 2
  let g0 := attacking (addPermanent battle rider caster caster) "Rider"
  let riderObj := obj g0 "Rider"
  let g0 := g0.record (GameEvent.attached g0.turnNumber (g0.snapshot riderObj) (pid g0 "Cub")
    (cause := .gameRule .staticAbility))
  let g := step g0 .onAttackEquippedGainDoubleStrike
  !strikes g "Rider" && !strikes g "Cub" && !strikes g "Bear"

#guard
  let g0 := attach battle "Axe" "Bear"
  let (g1, _) := g0.move (pid g0 "Axe") (.graveyard caster)
  let g := step g1 .onAttackEquippedGainDoubleStrike
  !strikes g "Bear"

/- Protection from everything is the controller's when the source was
cast, including after that source has left the battlefield. Otherwise
nothing is granted. -/
#guard
  let g0 := cast (addPermanent afterDraw ring caster caster) "Ring"
  let g := step g0 .onEnterIfCastProtectionEverything (some (pid g0 "Ring"))
  g.protectionFromEverything caster && !g.protectionFromEverything opp

#guard
  let g0 := insertObject afterDraw ring caster (.graveyard caster)
  let g0 := cast g0 "Ring"
  let g := step g0 .onEnterIfCastProtectionEverything (some (anyObj g0 "Ring").id)
  g.protectionFromEverything caster

#guard
  let g0 := addPermanent afterDraw ring caster caster
  let g := step g0 .onEnterIfCastProtectionEverything (some (pid g0 "Ring"))
  !g.protectionFromEverything caster

#guard
  let g := step afterDraw .onEnterIfCastProtectionEverything
  !g.protectionFromEverything caster

/- Printed notations stay intact. -/
#guard TriggeredAbility.onAttackEquippedGainDoubleStrike.effect.body ==
  Effect.triggerEquippedAttackersGainDoubleStrike.body
#guard TriggeredAbility.onEnterIfCastProtectionEverything.effect.body ==
  Effect.triggerProtectionEverything.body
#guard TriggeredAbility.toNotation .onAttackEquippedGainDoubleStrike ==
  "Whenever this creature attacks, that creature gains double strike until end of turn."
#guard TriggeredAbility.toNotation .onEnterIfCastProtectionEverything ==
  "When this permanent enters, if there is this permanent and every this permanent is permanent that was cast, you has protection from everything until your next turn."

end Mtg.Engine.GrantTests
