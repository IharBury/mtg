import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Fixture
import Mtg.Engine.Game
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Attack triggers without `YouAttackLeftover`

The Kingpin may pay 2 life so creatures assign combat damage equal to
toughness. Daredevil may exile the top card, pump when it is a Hero, and
play it this turn. Cosmic Cube looks at the top six and may cast one.
-/

namespace Mtg.Engine.YouAttackTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def me : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def resolve (g : Game) (ab : TriggeredAbility) (sourceId : Option ObjectId := none)
    (targets : Array Target := #[]) : Game :=
  g.applyTriggeredAbility me ab sourceId targets

def named (g : Game) (name : String) : GameObject :=
  namedPermanent g name

def lookedId (g : Game) (name : String) : Option ObjectId :=
  match g.pending with
  | .mayCastFromLooked _ ids _ =>
    ids.find? (fun id => (g.findObject? id).any (·.name == name))
  | _ => none

def exiled (g : Game) (name : String) : Option GameObject :=
  g.objects.find? (fun o => o.zone == .exile && o.name == name)

/- The shared “whenever you attack” effects resolve as constructors that
do not carry `YouAttackLeftover`. The printed sentence stays the Oracle line. -/
#guard TriggeredAbility.resolution
    (TriggeredAbility.onYouAttacking Effect.youAttackingPay2LifeToughness) ==
  .may (.loseLife (.fixed 2))
    (.grant .assignCombatDamageEqualToughness .creaturesYouControl) .ifYouDo
#guard TriggeredAbility.resolution
    (TriggeredAbility.onYouAttacking Effect.youAttackingExileTopHeroPump) ==
  .may (.exile .top .playThisTurn .ifHero) (.sequence [])
#guard TriggeredAbility.resolution
    (TriggeredAbility.onYouAttacking Effect.youAttackingLookSixCast) ==
  .revealLibrary (.top 6) (.mayCast .looked .greatestAttackingPower .withoutPaying)

#guard toString (TriggeredAbility.onYouAttacking Effect.youAttackingPay2LifeToughness) ==
  TriggeredAbility.youAttackingSentence .pay2LifeToughness
#guard toString (TriggeredAbility.onYouAttacking Effect.youAttackingExileTopHeroPump) ==
  TriggeredAbility.youAttackingSentence .exileTopHeroPump
#guard toString (TriggeredAbility.onYouAttacking Effect.youAttackingLookSixCast) ==
  TriggeredAbility.youAttackingSentence .lookSixCast

/- The Kingpin may pay 2 life. Declining and being unable to pay leave
power and combat damage alone. Paying does not change power; a 1/5 assigns
5, and a 2/2 still assigns 2. -/
def kingpinBoard : Game :=
  let g := addPermanent afterDraw theKingpinOfCrime me me
  let g := addPermanent g grizzlyBears me me
  let kp := named g "The Kingpin of Crime"
  (g.markAttacking kp.id (some (.player opp))).changeStatus kp.id (.summoningSick false)

def kingpinOffer : Game :=
  let kp := named kingpinBoard "The Kingpin of Crime"
  resolve kingpinBoard
    (TriggeredAbility.onYouAttacking Effect.youAttackingPay2LifeToughness) (some kp.id)

#guard
  match kingpinOffer.pending with
  | .fraChoice q .kingpinMayPay2Life => q == me
  | _ => false

def kingpinDeclines : Game :=
  mustApply kingpinOffer me .decline

#guard kingpinDeclines.pending == .none &&
  kingpinDeclines.assignCombatDamageEqualToughness == none &&
  (kingpinDeclines.player me).life == (kingpinBoard.player me).life &&
  logContains kingpinDeclines "wasn't paid"

def kingpinPays : Game :=
  mustApply kingpinOffer me .accept

#guard
  let kp := named kingpinPays "The Kingpin of Crime"
  let bears := named kingpinPays "Grizzly Bears"
  kingpinPays.power kp == 1 && kingpinPays.toughness kp == 5 &&
    kingpinPays.combatDamageAmount kp == 5 &&
    kingpinPays.combatDamageToAssign kp true == 5 &&
    kingpinPays.combatDamageAmount bears == 2 &&
    (kingpinPays.player me).life + 2 == (kingpinBoard.player me).life &&
    kingpinPays.assignCombatDamageEqualToughness == some me

def kingpinCantPay : Game :=
  let g := kingpinBoard.changePlayer me (.life 1)
  let kp := named g "The Kingpin of Crime"
  resolve g (TriggeredAbility.onYouAttacking Effect.youAttackingPay2LifeToughness)
    (some kp.id)

#guard kingpinCantPay.pending == .none &&
  kingpinCantPay.assignCombatDamageEqualToughness == none &&
  (kingpinCantPay.player me).life == 1 &&
  logContains kingpinCantPay "wasn't paid"

/- Daredevil may exile the top card. A non-Hero is playable without the
pump. A Hero pumps +2/+1 and is still playable. Declining exiles nothing.
A source that has left still exiles a Hero, without a pump. -/
def daredevilOffer (top : CardDef) : Game :=
  let g := addPermanent afterDraw daredevilManWithoutFear me me
  let g := addToLibraryTop g top me
  let dd := named g "Daredevil, Man Without Fear"
  resolve g (TriggeredAbility.onYouAttacking Effect.youAttackingExileTopHeroPump)
    (some dd.id)

#guard
  match (daredevilOffer lightningBolt).pending with
  | .fraChoice q (.daredevilMayExile _) => q == me
  | _ => false

def daredevilDeclines : Game :=
  mustApply (daredevilOffer lightningBolt) me .decline

#guard (daredevilDeclines.player me).library.size ==
    ((daredevilOffer lightningBolt).player me).library.size &&
  daredevilDeclines.pumpOf (named daredevilDeclines "Daredevil, Man Without Fear") == (0, 0) &&
  logContains daredevilDeclines "doesn't exile"

def daredevilBolt : Game :=
  mustApply (daredevilOffer lightningBolt) me .accept

#guard
  match exiled daredevilBolt "Lightning Bolt" with
  | some o =>
    daredevilBolt.mayPlayFromExile me o &&
      daredevilBolt.pumpOf (named daredevilBolt "Daredevil, Man Without Fear") == (0, 0)
  | none => false

def daredevilHero : Game :=
  mustApply (daredevilOffer mistyKnightHeroForHire) me .accept

#guard
  match exiled daredevilHero "Misty Knight, Hero for Hire" with
  | some o =>
    daredevilHero.mayPlayFromExile me o &&
      daredevilHero.pumpOf (named daredevilHero "Daredevil, Man Without Fear") == (2, 1)
  | none => false

def daredevilLeft : Game :=
  let g := addPermanent afterDraw daredevilManWithoutFear me me
  let g := addToLibraryTop g mistyKnightHeroForHire me
  let dd := named g "Daredevil, Man Without Fear"
  let (g, _) := g.move dd.id (.graveyard me) none
  let g := resolve g
    (TriggeredAbility.onYouAttacking Effect.youAttackingExileTopHeroPump) (some dd.id)
  mustApply g me .accept

#guard
  match exiled daredevilLeft "Misty Knight, Hero for Hire" with
  | some o =>
    daredevilLeft.mayPlayFromExile me o &&
      logContains daredevilLeft "no longer on the battlefield" &&
      !(daredevilLeft.battlefield.any (·.name == "Daredevil, Man Without Fear"))
  | none => false

def daredevilEmpty : Game :=
  let g := addPermanent afterDraw daredevilManWithoutFear me me
  let g := g.changePlayer me (.library #[])
  let dd := named g "Daredevil, Man Without Fear"
  let g := resolve g
    (TriggeredAbility.onYouAttacking Effect.youAttackingExileTopHeroPump) (some dd.id)
  mustApply g me .accept

#guard (daredevilEmpty.player me).library.isEmpty &&
  daredevilEmpty.pumpOf (named daredevilEmpty "Daredevil, Man Without Fear") == (0, 0) &&
  logContains daredevilEmpty "no cards"

/- Cosmic Cube looks at six cards. The mana-value limit is the greatest
power among attacking creatures. An empty library looks at nothing.
Declining puts the cards back. A cheap spell can be cast as it resolves;
a more expensive one cannot. -/
def cubeBoard (attacking : Bool) : Game :=
  let g := addPermanent afterDraw cosmicCube me me
  let g := addPermanent g grizzlyBears me me
  if attacking then
    let bears := named g "Grizzly Bears"
    g.markAttacking bears.id (some (.player opp))
  else g

def cubeLook (attacking : Bool) : Game :=
  let g := cubeBoard attacking
  let g := addToLibraryTop g hillGiant me
  let g := addToLibraryTop g mountain me
  let g := addToLibraryTop g lightningBolt me
  let cube := named g "Cosmic Cube"
  resolve g (TriggeredAbility.onYouAttacking Effect.youAttackingLookSixCast)
    (some cube.id)

def cubeQuiet : Game := cubeLook false
def cubeAttacking : Game := cubeLook true

#guard
  match cubeQuiet.pending with
  | .mayCastFromLooked p ids maxMv =>
    p == me && maxMv == 0 && ids.size == 6
  | _ => false

#guard
  match cubeAttacking.pending with
  | .mayCastFromLooked p ids maxMv =>
    p == me && maxMv == 2 && ids.size == 6 &&
      (lookedId cubeAttacking "Lightning Bolt").isSome &&
      (lookedId cubeAttacking "Hill Giant").isSome
  | _ => false

def cubeEmpty : Game :=
  let g := cubeBoard true
  let g := g.changePlayer me (.library #[])
  let cube := named g "Cosmic Cube"
  resolve g (TriggeredAbility.onYouAttacking Effect.youAttackingLookSixCast)
    (some cube.id)

#guard cubeEmpty.pending == .none && logContains cubeEmpty "No cards to look at"

def cubeDeclines : Game :=
  mustApply cubeAttacking me .decline

#guard cubeDeclines.pending == .none &&
  cubeDeclines.objects.any (fun o =>
    o.zone == .library me && o.name == "Lightning Bolt") &&
  logContains cubeDeclines "declines to cast" &&
  logContains cubeDeclines "on the bottom"

def cubeCasts : Game :=
  match lookedId cubeAttacking "Lightning Bolt" with
  | some bolt => mustApply cubeAttacking me (.cast bolt)
  | none => cubeAttacking

#guard cubeCasts.objects.any (fun o => o.name == "Lightning Bolt" && o.zone == .stack) &&
  logContains cubeCasts "on the bottom"

def cubeTooBig : Bool :=
  match lookedId cubeAttacking "Hill Giant" with
  | none => false
  | some giant =>
    match cubeAttacking.apply me (.cast giant) with
    | .error msg => mentions msg "mana value is greater"
    | .ok _ => false

#guard cubeTooBig

end Mtg.Engine.YouAttackTests
