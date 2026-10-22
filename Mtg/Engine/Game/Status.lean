import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.Counter
import Mtg.Engine.Deck
import Mtg.Engine.Mana
import Mtg.Engine.Rng
import Mtg.Engine.Rules
import Mtg.Engine.Turn
import Mtg.Engine.Zone

/-!
# Permanent status (CR 110.5)

The `Status` a permanent carries: tapping, damage, combat state, counters,
until-end-of-turn effects, and the `untilEotFields` table cleanup folds to
clear them (CR 514.3).
-/

namespace Mtg.Engine

/-- Permanent status (CR 110.5). Extra fields track combat and EOT pumps. -/
structure Status where
  tapped : Bool := false
  damage : Int := 0
  summoningSick : Bool := true
  /-- Until-end-of-turn +P/+T (cleared in cleanup, CR 514.3 / 613.4c). -/
  pump : Int × Int := (0, 0)
  attacking : Bool := false
  /-- Player this creature is attacking (CR 508.1). Set with `attacking`. -/
  attackingWhom : Option PlayerId := none
  /-- The planeswalker this creature is attacking, if it attacks one rather
  than a player (CR 506.3). `attackingWhom` is that planeswalker's
  controller. -/
  attackingPlaneswalker : Option ObjectId := none
  /-- Attacking creatures this creature is blocking (CR 509.1a / 510.1d). -/
  blocking : Array ObjectId := #[]
  /-- Set when this attacker becomes blocked (CR 509.1h). Remains true even if
  every blocking creature leaves combat. -/
  blocked : Bool := false
  /-- Non-mana activations this turn, for “only once each turn”. -/
  activationsThisTurn : Nat := 0
  /-- Indices of activated abilities of this object activated this turn
  (“Activate only once each turn”). -/
  abilitiesActivatedThisTurn : Array Nat := #[]
  /-- +1/+1 counters (CR 122.1). These do not wear off in cleanup. -/
  plusOnePlusOne : Nat := 0
  /-- Minus-one counters (CR 122.1a). -/
  minusOneMinusOne : Nat := 0
  /-- Loyalty counters on a planeswalker (CR 122.1 / 306.5). -/
  loyaltyCounters : Nat := 0
  /-- A loyalty ability of this permanent was activated this turn (CR 606.3). -/
  loyaltyActivatedThisTurn : Bool := false
  /-- This permanent is prepared (Reality Fracture). -/
  prepared : Bool := false
  /-- Keywords granted until end of turn (cleared in cleanup, CR 514.3).
  Printed keywords stay on `GameObject.printed`; this field is merged in
  `GameObject.printedOrUntilEot`. -/
  untilEotKeywords : Keywords := {}
  /-- This creature loses indestructible until end of turn (e.g. Smite). -/
  untilEotLosesIndestructible : Bool := false
  /-- If this creature would die this turn, exile it instead
  (CR 614.1 / 614.6). -/
  untilEotExileIfDies : Bool := false
  /-- Until-end-of-turn layer-7b setting of base P/T (e.g. Galion). -/
  setBasePT : Option (Int × Int) := none
  /-- This permanent is a creature in addition to its other types (CR 205.1a).
  Lasting effects such as Beorn's Hospitality's activation do not end. -/
  additionalCreature : Bool := false
  /-- Subtypes granted by a lasting type-changing effect. -/
  additionalSubtypes : Array String := #[]
  /-- Static abilities granted by a lasting effect (CR 611.2a). -/
  grantedStaticAbilities : Array StaticAbility := #[]
  /-- Triggered abilities granted by a lasting effect (e.g. a Saga chapter
  that gives the Saga landfall). -/
  grantedTriggeredAbilities : Array TriggeredAbility := #[]
  /-- Objects granting this permanent hexproof while they remain. -/
  hexproofGrantedBy : Array ObjectId := #[]
  /-- Objects preventing damage this permanent would deal while they remain. -/
  preventDamageGrantedBy : Array ObjectId := #[]
  /-- Dealt damage by a source with deathtouch since the last time
  state-based actions were checked (CR 704.5h). Cleared after that check. -/
  dealtDeathtouch : Bool := false
  /-- Hope counters (e.g. Dawn of a New Age). -/
  hope : Nat := 0
  /-- Charge counters (Gardenize). -/
  charge : Nat := 0
  /-- Stun counters (CR 122.1d). -/
  stun : Nat := 0
  /-- A once-each-turn triggered ability of this permanent has fired. -/
  firedOnceEachTurn : Bool := false
  /-- The optional action of a “Do this only once each turn” trigger has
  been chosen this turn (MSH 69). -/
  optionalOnceUsed : Bool := false
  /-- This permanent is an artifact in addition to its other types until
  end of turn (e.g. Stone by Sunlight). -/
  additionalArtifactUntilEot : Bool := false
  /-- Hone counters. Each grants +1/+0 to the equipped creature while this
  Equipment is attached (judge rulings on Dwalin / Sting). -/
  hone : Nat := 0
  /-- Shadow counters. A permanent with a shadow counter has shadow. -/
  shadow : Nat := 0
  /-- Phased out (CR 702.26). Treated as though it does not exist. -/
  phasedOut : Bool := false
  /-- Host this Aura or Equipment phased out with. -/
  phasedWith : Option ObjectId := none
  /-- This creature is its controller's Ring-bearer. -/
  ringBearer : Bool := false
  /-- Alliance modes chosen this turn (0 = add GGG, 1 = +1/+1 each, 2 = scry
  then draw). Reset as the turn ends. -/
  allianceModesChosen : Array Nat := #[]
  /-- Shield counters. A shield counter is removed instead of taking damage
  or being destroyed (CR 122.1b / Marvel Super Heroes). -/
  shield : Nat := 0
  /-- Finality counters. A permanent with a finality counter that would go
  to a graveyard from the battlefield is exiled instead (MSH release notes). -/
  finality : Nat := 0
  /-- This creature was declared as an attacker this turn (boast, CR 702.111). -/
  declaredAsAttackerThisTurn : Bool := false
  /-- A boast ability of this creature has been activated this turn. -/
  boastUsedThisTurn : Bool := false
  /-- Plan counters on a Plan enchantment. -/
  plan : Nat := 0
  /-- A power-up ability of this permanent has been activated (CR 702.193). -/
  powerUpUsed : Bool := false
  /-- How many times a power-up ability of this permanent has been activated.
  Wonder Man raises the lifetime limit above one (MSH). -/
  powerUpActivations : Nat := 0
  /-- This permanent became tapped this turn (Captain America, Living Legend). -/
  becameTappedThisTurn : Bool := false
  /-- You put a +1/+1 counter on this creature this turn (Kid Loki). -/
  gotPlusOneThisTurn : Bool := false
  /-- Sources that stop this permanent becoming untapped while they remain
  (Spider-Woman; Frozen in Ice is attached separately). -/
  cantUntapGrantedBy : Array ObjectId := #[]
  /-- This permanent is a creature in addition to its other types until EOT
  (I Am Iron Man). -/
  additionalCreatureUntilEot : Bool := false
  /-- The Mind Stone (or similar) has been harnessed. -/
  harnessed : Bool := false
  /-- This permanent is currently showing its back face (MSH modal DFC). -/
  transformed : Bool := false
  /-- Entered back-face-up because it is night and the front has daybound
  (MSH 191). Transform is illegal. -/
  cantTransform : Bool := false
  /-- Sources that make this permanent lose its printed abilities while they
  remain (The Wondrous Wasp; MSH 145 / 190). Later granted abilities still
  apply. -/
  losesAbilitiesGrantedBy : Array ObjectId := #[]
  /-- This permanent loses all abilities until end of turn. -/
  losesAbilitiesUntilEot : Bool := false
  /-- Modes chosen for the object's lifetime (Gollum, Riddle Master). -/
  chosenModes : Array Nat := #[]
  /-- Modes of The Vision chosen this turn. Cleared as the turn ends. -/
  modesChosenThisTurn : Array Nat := #[]
  /-- Until end of turn, base power equals the number of cards in your hand
  (Ms. Marvel). -/
  cardsInHandPowerUntilEot : Bool := false
  /-- Odd/even choice (Gollum). `none` until chosen; `some true` is odd. -/
  chosenOdd : Option Bool := none
  /-- Lore counters on a Saga (CR 714). -/
  lore : Nat := 0
  /-- Indestructible counters. -/
  indestructibleCounters : Nat := 0
  /-- Lifelink counters (Arwen, Mortal Queen). -/
  lifelinkCounters : Nat := 0
  /-- Creature type chosen as this permanent entered (Unexpected Party). -/
  chosenCreatureType : Option String := none
  /-- Creatures this player controls cannot block this attacker this turn
  (The Black Gate). Cleared in cleanup. -/
  cantBeBlockedByPlayer : Option PlayerId := none
  /-- Until end of turn, this creature can be blocked only by creatures with
  haste (Speed, Young Avenger). -/
  cantBeBlockedExceptByHasteUntilEot : Bool := false
  /-- This creature can't block this turn. -/
  cantBlockUntilEot : Bool := false
  /-- Mana spent to cast this spell (CR 601.2h). -/
  manaSpentToCast : Nat := 0
  /-- This permanent dealt damage this turn (Red Guardian; MSH 272). -/
  dealtDamageThisTurn : Bool := false
  /-- Until end of turn, these replace existing creature types and keep
  noncreature subtypes (Iron Man Armor; MSH 88). -/
  replacedCreatureTypesUntilEot : Option (Array String) := none
  /-- Until end of turn, this creature gets +1/+1 for each artifact you
  control (Iron Man Armor). -/
  pumpPerArtifactUntilEot : Bool := false
  /-- Influence counters (Palantír of Orthanc). -/
  influence : Nat := 0
  /-- This permanent is only a Food artifact (Supper for Spiders). -/
  onlyFoodArtifact : Bool := false
  /-- Burden counters (The One Ring). -/
  burden : Nat := 0
  /-- Quest counters (Last Light of Durin's Day). -/
  quest : Nat := 0
  /-- Invasion counters (Alien Invasion). -/
  invasion : Nat := 0
  /-- Trample counters (Beorn the Fierce). -/
  trampleCounters : Nat := 0
  /-- Haste, flying, and the other keyword counters Super-Adaptoid copies.
  Trample, lifelink, and indestructible use their own fields. -/
  keywordCounters : KeywordCounters := {}
  /-- Until end of turn, combat damage to a player creates a Treasure. -/
  combatDamageCreatesTreasure : Bool := false
  /-- This permanent is an artifact and not a creature (Tom, Bert, and William). -/
  returnedAsArtifact : Bool := false
  /-- A control-changing effect lasts until end of turn (Act of Treason,
  Sauron, the Lidless Eye). Cleared in cleanup; ending it may exile (CR 800.4c). -/
  controlUntilEot : Bool := false
  /-- Endings of this object's controller's turns before control reverts
  (Evil's Thrall: 2 means until the end of your next turn). -/
  controlTurnEndsLeft : Nat := 0
  /-- Instances of Iron Fist's granted tap ability this turn (MSH 106). -/
  ironFistTapGrants : Nat := 0
  /-- +P/+T lasting until the listed player's next turn begins (Garruk,
  Veiled Butcher). -/
  untilTurnOfPump : Array (PlayerId × Int × Int) := #[]
  /-- Triggered abilities granted until end of turn (Lyra, Tolarian
  Archangel). -/
  grantedTriggersUntilEot : Array TriggeredAbility := #[]
  /-- An exhaust ability of this permanent has been activated (CR 702.177). -/
  exhaustUsed : Bool := false
  /-- This land has “{T}: Add {C}{C}” until the exiled card with this id is
  cast from exile (Emrakul, the Exigent Doom; rulings 729 / 730). -/
  colorlessGrantUntilCast : Array ObjectId := #[]
  /-- Color chosen as this permanent entered (Room of Refuge). -/
  chosenColor : Option Color := none
  /-- This permanent has dealt combat damage since it entered (Ruric Thar). -/
  dealtCombatDamage : Bool := false
  /-- Players this creature dealt combat damage to this turn (Witch-king of Angmar). -/
  combatDamageToPlayers : Array PlayerId := #[]
  /-- An attached Aura makes this a 5/5 Construct creature in addition to its
  other types (Puppet Crafting). Refreshed with state-based actions. -/
  animatedConstruct55 : Bool := false
  /-- Card name chosen as this permanent entered (Meddling Mage). -/
  chosenName : Option String := none
  /-- Face down (morph, CR 702.37). A 2/2 creature with no abilities. -/
  faceDown : Bool := false
  /-- Goaded for as long as this flag remains (CR 701.38). -/
  goaded : Bool := false
  /-- Story counters (Staff of the Storyteller). -/
  story : Nat := 0
  /-- Time counters (impending, CR 702.176). -/
  time : Nat := 0
  /-- This permanent is not a creature (impending, until the last time counter). -/
  notACreature : Bool := false
  /-- Windcrag Siege chose Mardu. Jeskai is `false`. -/
  windcragMardu : Bool := true
  /-- Card type chosen as this permanent entered (Serra's Emissary). -/
  chosenCardType : Option String := none
  /-- This card may be cast from its owner's graveyard without paying its
  mana cost, ignoring timing, until end of turn. -/
  freeCastFromGraveyard : Bool := false
  /-- This permanent is a commander. -/
  isCommander : Bool := false
  /-- First strike only during its controller's turn, until end of turn. -/
  firstStrikeOnYourTurn : Bool := false
deriving Repr, Inhabited, BEq

namespace Status

/-- Until-end-of-turn power bonus. -/
def pumpPower (s : Status) : Int := s.pump.1

/-- Until-end-of-turn toughness bonus. -/
def pumpToughness (s : Status) : Int := s.pump.2

/-- Until-end-of-turn layer-7b base power, if set. -/
def setBasePower (s : Status) : Option Int := s.setBasePT.map (·.1)

/-- Until-end-of-turn layer-7b base toughness, if set. -/
def setBaseToughness (s : Status) : Option Int := s.setBasePT.map (·.2)

/-- True when this permanent has a counter (CR 122.1). -/
def hasCounters (s : Status) : Bool :=
  s.plusOnePlusOne > 0 || s.minusOneMinusOne > 0 || s.loyaltyCounters > 0 || s.hope > 0 ||
    s.charge > 0 ||
    s.stun > 0 || s.shield > 0 ||
    s.finality > 0 || s.plan > 0 || s.burden > 0 || s.quest > 0 || s.invasion > 0 ||
    s.influence > 0 || s.trampleCounters > 0 || s.indestructibleCounters > 0 ||
    s.lifelinkCounters > 0 || s.hone > 0 || s.shadow > 0 || s.lore > 0 ||
    s.story > 0 || s.time > 0 ||
    s.keywordCounters.any

/-- True when cleanup must clear until-EOT pumps, damage, keyword grants, or
base P/T setting (CR 514.3). -/
def clearsAtCleanup (s : Status) : Bool :=
  s.damage != 0 || s.pump != (0, 0) || s.untilEotKeywords != Keywords.none ||
  s.untilEotLosesIndestructible || s.untilEotExileIfDies || s.setBasePT.isSome ||
  s.additionalArtifactUntilEot || s.additionalCreatureUntilEot ||
  s.cantBeBlockedByPlayer.isSome || s.cantBeBlockedExceptByHasteUntilEot ||
  s.cantBlockUntilEot || s.dealtDamageThisTurn ||
  s.replacedCreatureTypesUntilEot.isSome || s.pumpPerArtifactUntilEot ||
  s.ironFistTapGrants != 0 || s.losesAbilitiesUntilEot ||
  !s.grantedTriggersUntilEot.isEmpty || s.cardsInHandPowerUntilEot ||
  s.firstStrikeOnYourTurn

end Status

#guard
  let s : Status := { pump := (1, 2), damage := 3, setBasePT := some (4, 4) }
  s.clearsAtCleanup && s.pumpPower == 1 && s.pumpToughness == 2 &&
    s.setBasePower == some 4
#guard !({} : Status).clearsAtCleanup

end Mtg.Engine
