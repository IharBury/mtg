import Mtg.Engine.Fixture

/-!
# `TriggerResolution.mayCast`

Graveyard casts, hand casts limited by legendary Wizards, hand casts limited
by last-known damage, and the impulse cast after
`revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer`.
-/

namespace Mtg.Engine.MayCastTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def victim : PlayerId := ⟨1⟩

def wizard : CardDef := {
  name := "Test Wizard"
  types := #[.creature]
  supertypes := #[.legendary]
  subtypes := #["Human", "Wizard"]
  power := some 1
  toughness := some 1
}

def costly : CardDef := {
  name := "Costly Sorcery"
  manaCost := ManaCost.ofGeneric 4
  types := #[.sorcery]
}

def bauble : CardDef := {
  name := "Test Bauble"
  types := #[.artifact]
}

def putInHand (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.hand p) none {} (fun id _ => #[.pushHand id])

def putInGraveyard (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.graveyard p) none {} (fun id _ =>
    #[.pushGraveyard id])

def putOnLibrary (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.library p) none {} (fun id _ =>
    #[.pushLibrary id])

def namedId (g : Game) (ids : Array ObjectId) (name : String) : Option ObjectId :=
  ids.find? (fun id => (g.findObject? id).any (·.name == name))

def permanentId (g : Game) (name : String) : Option ObjectId :=
  match g.battlefield.find? (fun o => o.name == name) with
  | some o => some o.id
  | none => none

def inList (g : Game) (ids : Array ObjectId) (name : String) : Bool :=
  (namedId g ids name).isSome

def inExile (g : Game) (name : String) : Bool :=
  g.objects.any (fun o => o.name == name && o.zone == .exile)

def onStack (g : Game) (name : String) : Bool :=
  g.objects.any (fun o => o.name == name && o.zone == .stack)

def onBattlefield (g : Game) (name : String) : Bool :=
  g.objects.any (fun o => o.name == name && o.zone == .battlefield)

def withRed (g : Game) (p : PlayerId) (n : Nat) : Game :=
  g.changePlayer p (.addMana (.colored .red) n)

/- One legendary Wizard makes the hand limit 2. Shock is offered; a
mana value 4 sorcery is not. Declining leaves both in hand. -/
#guard
  let g := putInHand (putInHand (addPermanent afterDraw wizard caster caster) shock caster)
    costly caster
  let src := permanentId g "Test Wizard"
  let g := g.applyTriggeredAbility caster .onYourBeginCombatCastInstantSorceryFromHand src
  let shockId := namedId g (g.player caster).hand "Shock"
  let offered :=
    match shockId, g.pending with
    | some id, .fraChoice _ (.mayCastInstantSorceryFromHand eligible) =>
      eligible.contains id &&
        !eligible.any (fun i => (g.object! i).name == "Costly Sorcery")
    | _, _ => false
  let logged := g.log.any (fun s => mentions s "mana value 2 or less")
  let g := mustApply g caster .decline
  offered && logged && inList g (g.player caster).hand "Shock" &&
    inList g (g.player caster).hand "Costly Sorcery" && !onStack g "Shock"

/- Accepting casts Shock from hand without paying and leaves the sorcery. -/
#guard
  let g := putInHand (putInHand (addPermanent afterDraw wizard caster caster) shock caster)
    costly caster
  let src := permanentId g "Test Wizard"
  let g := g.applyTriggeredAbility caster .onYourBeginCombatCastInstantSorceryFromHand src
  match namedId g (g.player caster).hand "Shock" with
  | none => false
  | some shockId =>
    let g := mustApply g caster (.choosePermanents #[shockId])
    onStack g "Shock" && inList g (g.player caster).hand "Costly Sorcery" &&
      (match g.pending with | .chooseTargets _ => true | _ => false)

/- Last-known damage 1 offers Shock and not a mana value 4 sorcery. -/
#guard
  let g := putInHand (putInHand afterDraw shock caster) costly caster
  let g := g.applyTriggeredAbility caster .onEquippedCombatDamageCastInstantSorcery
    none (lastKnownPower := some 1)
  match namedId g (g.player caster).hand "Shock", g.pending with
  | some id, .fraChoice _ (.mayCastInstantSorceryFromHand eligible) =>
    eligible.contains id &&
      !eligible.any (fun i => (g.object! i).name == "Costly Sorcery") &&
      g.log.any (fun s => mentions s "mana value 1 or less")
  | _, _ => false

/- A graveyard creature is not offered. Declining leaves the instant there. -/
#guard
  let g := putInGraveyard (putInGraveyard afterDraw shock caster) grizzlyBears caster
  let g := g.applyTriggeredAbility caster .onAttackCastFromGyArtifactInstantSorcery none
  match namedId g (g.player caster).graveyard "Shock" with
  | none => false
  | some shockId =>
    let offered :=
      match g.pending with
      | .fraChoice _ (.mayCastFromGraveyard ids) =>
        ids.contains shockId &&
          !ids.any (fun i => (g.object! i).name == "Grizzly Bears")
      | _ => false
    let g := mustApply g caster .decline
    offered && inList g (g.player caster).graveyard "Shock" && g.stack.isEmpty

/- Paying for that instant exiles it instead of putting it in the graveyard. -/
#guard
  let g := putInGraveyard afterDraw shock caster
  let g := withRed g caster 1
  let g := g.applyTriggeredAbility caster .onAttackCastFromGyArtifactInstantSorcery none
  match namedId g (g.player caster).graveyard "Shock" with
  | none => false
  | some shockId =>
    let g := mustApply g caster (.cast shockId)
    let g := mustApply g caster (.target (.player victim))
    let g := passBoth (mustApply g caster .pay)
    inExile g "Shock" && !inList g (g.player caster).graveyard "Shock" &&
      (g.player victim).life == 18

/- An artifact cast from the graveyard enters the battlefield. -/
#guard
  let g := putInGraveyard afterDraw bauble caster
  let g := g.applyTriggeredAbility caster .onAttackCastFromGyArtifactInstantSorcery none
  match namedId g (g.player caster).graveyard "Test Bauble" with
  | none => false
  | some id =>
    let g := passBoth (mustApply g caster (.cast id))
    onBattlefield g "Test Bauble" && !inExile g "Test Bauble"

/- Declining the impulse returns every exiled card. Accepting casts the
instant and bottoms only the cards that were not cast. -/
#guard
  let g := addPermanent (putOnLibrary (putOnLibrary afterDraw lightningBolt victim) mountain victim)
    wizard caster caster
  let g := g.noteCombatDamageTo victim (g.object! (permanentId g "Test Wizard").get!).asEvent
  let g := g.applyTriggeredAbility caster .onCombatDamageImpulseInstantSorcery none
  let offered :=
    match g.pending with
    | .fraChoice p (.mayCastGrima _ _ v) => p == caster && v == victim
    | _ => false
  let g := mustApply g caster .decline
  offered &&
    inList g (g.player victim).library "Lightning Bolt" &&
    inList g (g.player victim).library "Mountain" &&
    !inExile g "Lightning Bolt" && !inExile g "Mountain" &&
    !onStack g "Lightning Bolt" &&
    g.log.any (fun s => mentions s "face up")

#guard
  let g := addPermanent (putOnLibrary (putOnLibrary afterDraw lightningBolt victim) mountain victim)
    wizard caster caster
  let g := g.noteCombatDamageTo victim (g.object! (permanentId g "Test Wizard").get!).asEvent
  let g := g.applyTriggeredAbility caster .onCombatDamageImpulseInstantSorcery none
  let g := mustApply g caster .accept
  onStack g "Lightning Bolt" &&
    g.log.any (fun s => mentions s "as the ability resolves") &&
    (g.object! (g.player victim).library[0]!).name == "Mountain" &&
    !inExile g "Mountain" &&
    (match g.pending with | .chooseTargets _ => true | _ => false)

end Mtg.Engine.MayCastTests
