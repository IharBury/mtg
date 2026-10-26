import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Fixture
import Mtg.Engine.Game
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Cast triggers without `CastLeftover`

Each leftover “whenever you cast …” effect resolves as the constructors
that effect uses. `CastLeftover` stays the printed sentence.
-/

namespace Mtg.Engine.CastingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def me : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def resolve (g : Game) (ab : TriggeredAbility) (sourceId : Option ObjectId := none)
    (targets : Array Target := #[]) (lastKnownPower : Option Int := none) : Game :=
  g.applyTriggeredAbility me ab sourceId targets (lastKnownPower := lastKnownPower)

def named (g : Game) (name : String) : GameObject :=
  namedPermanent g name

def tokensNamed (g : Game) (name : String) : Nat :=
  (g.battlefield.filter fun o => o.printed.isToken && o.name == name).size

/-- Put `spell` on the stack as the cause of `source`'s resolving ability. -/
def withCause (g : Game) (source : GameObject) (spell : CardDef)
    (targets : Array Target := #[]) (x : Option Nat := none) : Game :=
  let (g, spellObj) := g.allocObject spell me .stack (some me)
  let g := g.changeObject spellObj.id (.chosenX x)
  let g := g.putStackEntry me spellObj.id
  let g :=
    if targets.isEmpty then g
    else g.changeStackEntryById spellObj.id (.targets targets)
  let (g, ab) := g.allocStackAbility source me
  let g := g.changeObject ab.id (.fraCauseId (some spellObj.id))
  g.change (.resolvingAbility (some ab.id))

def casting (e : Effect) : TriggeredAbility :=
  TriggeredAbility.onCasting e

/- The shared cast effects resolve as constructors that do not carry
`CastLeftover`. The printed sentence stays the Oracle line. -/
#guard TriggeredAbility.resolution (casting Effect.castingVillainToken) ==
  .createTokens .villain21menace (.fixed 1) false
#guard TriggeredAbility.resolution (casting Effect.castingMerfolkFromBlue) ==
  .createTokens .treasure .blueManaSymbols false .merfolk
#guard TriggeredAbility.resolution (casting Effect.castingMayPayHasteUnblockable) ==
  .may (.pay (.mana #[.generic 1])) (.queueReflexive (.cant (.beBlockedExceptByHaste .target))) .ifYouDo
#guard TriggeredAbility.resolution (casting Effect.castingPlusOneEachOther) ==
  .putCounters (.ofKind .plusOnePlusOne) .eachOther
#guard TriggeredAbility.resolution (casting Effect.castingExileFlicker) ==
  .exile .target .nextEndStep
#guard TriggeredAbility.resolution (casting Effect.castingVisionModes) ==
  .chooseModes TriggeredAbility.TriggerResolution.visionModes .vision
#guard TriggeredAbility.resolution (casting Effect.castingDamageEqualMv) ==
  .dealDamage .spellManaValue .target
#guard TriggeredAbility.resolution (casting Effect.castingDrawPowerEqualHand) ==
  .sequence [.draw (.fixed 1), .grant .basePowerEqualHand .source]
#guard TriggeredAbility.resolution (casting Effect.castingPlusOneThis) ==
  .putCounters (.ofKind .plusOnePlusOne) .source
#guard TriggeredAbility.resolution (casting Effect.castingPlusOneScry) ==
  .sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .scry (.fixed 1)]
#guard TriggeredAbility.resolution (casting Effect.castingIronFistTap) ==
  .grant .ironFistTap .source
#guard TriggeredAbility.resolution (casting Effect.castingTargetsGainFlying) ==
  .grant (.keywords Keyword.flying) .spellTargets
#guard TriggeredAbility.resolution (casting Effect.castingCopyIfArtifactOrLand) ==
  .sequence [.putCounters (.ofKind .plusOnePlusOne 2) .source, .copyCause]
#guard TriggeredAbility.resolution (casting Effect.castingTapCreatureOrLand) ==
  .tap .target

#guard toString (casting Effect.castingVillainToken) ==
  TriggeredAbility.castingSentence .villainToken
#guard toString (casting Effect.castingMerfolkFromBlue) ==
  TriggeredAbility.castingSentence .merfolkFromBlue
#guard toString (casting Effect.castingMayPayHasteUnblockable) ==
  TriggeredAbility.castingSentence .mayPayHasteUnblockable
#guard toString (casting Effect.castingPlusOneEachOther) ==
  TriggeredAbility.castingSentence .plusOneEachOther
#guard toString (casting Effect.castingExileFlicker) ==
  TriggeredAbility.castingSentence .exileFlicker
#guard toString (casting Effect.castingVisionModes) ==
  TriggeredAbility.castingSentence .visionModes
#guard toString (casting Effect.castingDamageEqualMv) ==
  TriggeredAbility.castingSentence .damageEqualMv
#guard toString (casting Effect.castingDrawPowerEqualHand) ==
  TriggeredAbility.castingSentence .drawPowerEqualHand
#guard toString (casting Effect.castingPlusOneThis) ==
  TriggeredAbility.castingSentence .plusOneThis
#guard toString (casting Effect.castingPlusOneScry) ==
  TriggeredAbility.castingSentence .plusOneScry
#guard toString (casting Effect.castingIronFistTap) ==
  TriggeredAbility.castingSentence .ironFistTap
#guard toString (casting Effect.castingTargetsGainFlying) ==
  TriggeredAbility.castingSentence .targetsGainFlying
#guard toString (casting Effect.castingCopyIfArtifactOrLand) ==
  TriggeredAbility.castingSentence .copyIfArtifactOrLand
#guard toString (casting Effect.castingTapCreatureOrLand) ==
  TriggeredAbility.castingSentence .tapCreatureOrLand

/- A Villain spell creates one 2/1 Villain token with menace. -/
def villainBoard : Game :=
  addPermanent afterDraw volcanicVillain me me

def villainTokens : Game :=
  let src := named villainBoard "Volcanic Villain"
  resolve villainBoard (casting Effect.castingVillainToken) (some src.id)

#guard
  let tok := named villainTokens "Villain"
  tokensNamed villainTokens "Villain" == 1 &&
    villainTokens.power tok == 2 && villainTokens.toughness tok == 1 &&
    villainTokens.hasMenace tok

/- Namor creates one Merfolk for each blue mana symbol. A red spell creates none. -/
def namorBoard : Game :=
  addPermanent afterDraw namorTheSubMariner me me

def namorBlue : Game :=
  let src := named namorBoard "Namor the Sub-Mariner"
  resolve (withCause namorBoard src secretInvasion) (casting Effect.castingMerfolkFromBlue)
    (some src.id)

def namorRed : Game :=
  let src := named namorBoard "Namor the Sub-Mariner"
  resolve (withCause namorBoard src lightningBolt) (casting Effect.castingMerfolkFromBlue)
    (some src.id)

#guard tokensNamed namorBlue "Merfolk" == 2 &&
  tokensNamed namorRed "Merfolk" == 0 &&
  logContains namorRed "No blue mana symbols"

/- Speed may pay {1}. Declining queues nothing. Paying makes a hasty creature
unblockable except by haste. -/
def speedBoard : Game :=
  let g := addPermanent afterDraw speedYoungAvenger me me
  addPermanent g volcanicVillain me me

def speedOffer : Game :=
  let src := named speedBoard "Speed, Young Avenger"
  resolve speedBoard (casting Effect.castingMayPayHasteUnblockable) (some src.id)

#guard
  match speedOffer.pending with
  | .fraChoice q (.mayPayManaForReflexive cost _ 9 _) =>
    q == me && cost == #[.generic 1]
  | _ => false

def speedDeclines : Game :=
  mustApply speedOffer me .decline

#guard speedDeclines.pending == .none && !speedDeclines.hasModeledReflexiveOnStack &&
  logContains speedDeclines "isn't paid"

def speedPays : Game :=
  let g := speedOffer.changePlayer me (.addMana (.colored .green) 1)
  let g := mustApply g me .accept
  g.applyModeledReflexive #[Target.permanent (named g "Volcanic Villain").id]

#guard
  let villain := named speedPays "Volcanic Villain"
  !speedPays.hasModeledReflexiveOnStack &&
    villain.status.cantBeBlockedExceptByHasteUntilEot

/- A +1/+1 counter goes on each other creature, not the source. -/
def eachOtherBoard : Game :=
  let g := addPermanent afterDraw namorTheSubMariner me me
  addPermanent g grizzlyBears me me

def eachOther : Game :=
  let src := named eachOtherBoard "Namor the Sub-Mariner"
  resolve eachOtherBoard (casting Effect.castingPlusOneEachOther) (some src.id)

#guard
  (named eachOther "Namor the Sub-Mariner").status.plusOnePlusOne == 0 &&
    (named eachOther "Grizzly Bears").status.plusOnePlusOne == 1

/- Wiccan exiles another nonland nontoken until the next end step.
A token is not a legal target. -/
def wiccanBoard : Game :=
  let g := addPermanent afterDraw wiccanRisingMagician me me
  let g := addPermanent g grizzlyBears me me
  let g := addPermanent g hillGiant me me
  let giant := named g "Hill Giant"
  g.changeObject giant.id (.printed { giant.printed with isToken := true })

def wiccanExiles : Game :=
  let src := named wiccanBoard "Wiccan, Rising Magician"
  let bears := named wiccanBoard "Grizzly Bears"
  resolve wiccanBoard (casting Effect.castingExileFlicker) (some src.id)
    #[Target.permanent bears.id]

def wiccanMisses : Game :=
  let src := named wiccanBoard "Wiccan, Rising Magician"
  let giant := named wiccanBoard "Hill Giant"
  resolve wiccanBoard (casting Effect.castingExileFlicker) (some src.id)
    #[Target.permanent giant.id]

#guard !wiccanExiles.battlefield.any (fun o => o.name == "Grizzly Bears") &&
  wiccanExiles.delayedEndStepReturns.size == 1 &&
  wiccanMisses.battlefield.any (fun o => o.name == "Hill Giant") &&
  logContains wiccanMisses "no longer legal"

/- The Vision chooses one unused mode. A used set does nothing. Drawing
still happens after the Vision has left. -/
def visionBoard : Game :=
  addPermanent afterDraw theVision me me

def visionOffer : Game :=
  let src := named visionBoard "The Vision"
  resolve visionBoard (casting Effect.castingVisionModes) (some src.id)

def visionStrike : Game :=
  mustApply visionOffer me (.chooseMode 0)

#guard
  match visionOffer.pending with
  | .fraChoice _ (.visionMode _ available) => available == #[0, 1, 2]
  | _ => false

#guard
  let vis := named visionStrike "The Vision"
  visionStrike.hasDoubleStrike vis && vis.status.modesChosenThisTurn == #[0]

def visionDraw : Game :=
  let src := named visionBoard "The Vision"
  let g := resolve visionBoard (casting Effect.castingVisionModes) (some src.id)
  mustApply g me (.chooseMode 2)

#guard (visionDraw.player me).hand.size == (visionBoard.player me).hand.size + 1 &&
  (named visionDraw "The Vision").status.modesChosenThisTurn == #[2]

def visionExhausted : Game :=
  let g := visionBoard
  let src := named g "The Vision"
  let g := g.changeStatus src.id (.modesChosenThisTurn #[0, 1, 2])
  resolve g (casting Effect.castingVisionModes) (some (named g "The Vision").id)

#guard (visionExhausted.player me).hand.size == (visionBoard.player me).hand.size &&
  visionExhausted.pending == .none &&
  logContains visionExhausted "removed from the stack"

def visionLeftDraws : Game :=
  let src := named visionBoard "The Vision"
  let g := (visionBoard.move src.id (.graveyard me) none).1
  let g := resolve g (casting Effect.castingVisionModes) (some src.id)
  mustApply g me (.chooseMode 2)

#guard (visionLeftDraws.player me).hand.size == (visionBoard.player me).hand.size + 1

/- Thor deals damage equal to the causing spell's mana value, including X.
No recorded spell uses the last-known power. -/
def thorBoard : Game :=
  addPermanent afterDraw thorGodOfThunder me me

def thorDamage (spell : Option CardDef := none) (x : Option Nat := none)
    (lastKnown : Option Int := none) : Game :=
  let src := named thorBoard "Thor, God of Thunder"
  let g :=
    match spell with
    | some face => withCause thorBoard src face (x := x)
    | none => thorBoard
  resolve g (casting Effect.castingDamageEqualMv) (some src.id)
    #[Target.player opp] lastKnown

#guard ((thorDamage (some secretInvasion)).player opp).life == 17 &&
  ((thorDamage (some secretInvasion) (x := some 2)).player opp).life == 15 &&
  ((thorDamage (lastKnown := some 4)).player opp).life == 16

/- Ms. Marvel draws, then her base power is the number of cards in hand.
A source that has left still draws. -/
def marvelBoard : Game :=
  addPermanent afterDraw msMarvelKamalaKhan me me

def marvelDraws : Game :=
  let src := named marvelBoard "Ms. Marvel, Kamala Khan"
  resolve marvelBoard (casting Effect.castingDrawPowerEqualHand) (some src.id)

#guard
  let marvel := named marvelDraws "Ms. Marvel, Kamala Khan"
  let fromHand := Int.ofNat (marvelDraws.player me).hand.size
  marvel.status.cardsInHandPowerUntilEot && marvelDraws.power marvel == fromHand &&
    (marvelBoard.player me).hand.size + 1 == (marvelDraws.player me).hand.size

def marvelLeft : Game :=
  let src := named marvelBoard "Ms. Marvel, Kamala Khan"
  let g := (marvelBoard.move src.id (.graveyard me) none).1
  resolve g (casting Effect.castingDrawPowerEqualHand) (some src.id)

#guard (marvelLeft.player me).hand.size == (marvelBoard.player me).hand.size + 1 &&
  logContains marvelLeft "The source is no longer in play"

/- Mockingbird gets a +1/+1 counter. A source that has left does not. -/
def birdBoard : Game :=
  addPermanent afterDraw mockingbirdAceAgent me me

def birdCounter : Game :=
  let src := named birdBoard "Mockingbird, Ace Agent"
  resolve birdBoard (casting Effect.castingPlusOneThis) (some src.id)

#guard (named birdCounter "Mockingbird, Ace Agent").status.plusOnePlusOne == 1

def birdLeft : Game :=
  let src := named birdBoard "Mockingbird, Ace Agent"
  let g := (birdBoard.move src.id (.graveyard me) none).1
  resolve g (casting Effect.castingPlusOneThis) (some src.id)

#guard logContains birdLeft "The triggered ability's source is no longer in play"

/- Colleen Wing gets a +1/+1 counter, then scries 1. -/
def colleenBoard : Game :=
  addPermanent afterDraw colleenWingStreetSamurai me me

def colleenScry : Game :=
  let src := named colleenBoard "Colleen Wing, Street Samurai"
  resolve colleenBoard (casting Effect.castingPlusOneScry) (some src.id)

#guard
  match colleenScry.pending with
  | .scry q n _ =>
    q == me && n == 1 &&
      (named colleenScry "Colleen Wing, Street Samurai").status.plusOnePlusOne == 1
  | _ => false

/- Iron Fist gains one tap ability each time. A source that has left gains none. -/
def fistBoard : Game :=
  addPermanent afterDraw ironFistLivingWeapon me me

def fistTap : Game :=
  let src := named fistBoard "Iron Fist, Living Weapon"
  let g := resolve fistBoard (casting Effect.castingIronFistTap) (some src.id)
  resolve g (casting Effect.castingIronFistTap) (some (named g "Iron Fist, Living Weapon").id)

#guard (named fistTap "Iron Fist, Living Weapon").status.ironFistTapGrants == 2

def fistLeft : Game :=
  let src := named fistBoard "Iron Fist, Living Weapon"
  let g := (fistBoard.move src.id (.graveyard me) none).1
  resolve g (casting Effect.castingIronFistTap) (some src.id)

#guard logContains fistLeft "The source is no longer in play" &&
  match (fistLeft.player me).graveyard.back? with
  | some id =>
    match fistLeft.findObject? id with
    | some o => o.status.ironFistTapGrants == 0
    | none => false
  | none => false

/- Creature targets of the causing spell gain flying. A land does not. -/
def flyingBoard : Game :=
  let g := addPermanent afterDraw theVision me me
  let g := addPermanent g grizzlyBears opp opp
  addPermanent g mountain opp opp

def flyingGrant : Game :=
  let src := named flyingBoard "The Vision"
  let bears := named flyingBoard "Grizzly Bears"
  let land := named flyingBoard "Mountain"
  resolve (withCause flyingBoard src lightningBolt
      #[Target.permanent bears.id, Target.permanent land.id])
    (casting Effect.castingTargetsGainFlying) (some src.id)

#guard flyingGrant.hasFlying (named flyingGrant "Grizzly Bears") &&
  !flyingGrant.hasFlying (named flyingGrant "Mountain")

/- Fin Fang Foom copies the causing spell and gets two +1/+1 counters.
A source that has left still copies. -/
def foomBoard : Game :=
  addPermanent afterDraw finFangFoom me me

def foomCopy : Game :=
  let src := named foomBoard "Fin Fang Foom"
  resolve (withCause foomBoard src lightningBolt) (casting Effect.castingCopyIfArtifactOrLand)
    (some src.id)

#guard
  match foomCopy.pending with
  | .fraChoice q (.newTargetsForCopies _) =>
    q == me && (named foomCopy "Fin Fang Foom").status.plusOnePlusOne == 2
  | _ => false

def foomLeft : Game :=
  let src := named foomBoard "Fin Fang Foom"
  let g := (foomBoard.move src.id (.graveyard me) none).1
  resolve (withCause g src lightningBolt) (casting Effect.castingCopyIfArtifactOrLand)
    (some src.id)

#guard
  match foomLeft.pending with
  | .fraChoice _ (.newTargetsForCopies _) =>
    logContains foomLeft "The triggered ability's source is no longer in play"
  | _ => false

/- Quake taps a creature or a land. An enchantment is not legal. -/
def quakeBoard : Game :=
  let g := addPermanent afterDraw quakeAgentOfSHIELD me me
  let g := addPermanent g mountain opp opp
  addPermanent g heroicFeast opp opp

def quakeTaps : Game :=
  let src := named quakeBoard "Quake, Agent of S.H.I.E.L.D."
  let land := named quakeBoard "Mountain"
  resolve quakeBoard (casting Effect.castingTapCreatureOrLand) (some src.id)
    #[Target.permanent land.id]

def quakeMisses : Game :=
  let src := named quakeBoard "Quake, Agent of S.H.I.E.L.D."
  let feast := named quakeBoard "Heroic Feast"
  resolve quakeBoard (casting Effect.castingTapCreatureOrLand) (some src.id)
    #[Target.permanent feast.id]

#guard (named quakeTaps "Mountain").status.tapped &&
  !(named quakeMisses "Heroic Feast").status.tapped &&
  logContains quakeMisses "no longer legal"

end Mtg.Engine.CastingTests
