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

/-- Until-end-of-turn continuous effects on a permanent, cleared during the cleanup step (CR 514.3 / CR 611.2a). -/
structure UntilEotStatus where
  /-- Until-end-of-turn +P/+T (cleared in cleanup, CR 514.3 / 613.4c). -/
  pump : Int × Int := (0, 0)
  /-- Until-end-of-turn layer-7b setting of base P/T (e.g. Galion). -/
  setBasePT : Option (Int × Int) := none
  /-- This permanent is an artifact in addition to its other types until
  end of turn (e.g. Stone by Sunlight). -/
  additionalArtifactUntilEot : Bool := false
  /-- This permanent is a creature in addition to its other types until EOT
  (I Am Iron Man). -/
  additionalCreatureUntilEot : Bool := false
  /-- Until end of turn, base power equals the number of cards in your hand
  (Ms. Marvel). -/
  cardsInHandPowerUntilEot : Bool := false
  /-- Until end of turn, these replace existing creature types and keep
  noncreature subtypes (Iron Man Armor; MSH 88). -/
  replacedCreatureTypesUntilEot : Option (Array String) := none
  /-- Until end of turn, this creature gets +1/+1 for each artifact you
  control (Iron Man Armor). -/
  pumpPerArtifactUntilEot : Bool := false
  /-- Keywords granted until end of turn (cleared in cleanup, CR 514.3).
  Printed keywords stay on `GameObject.printed`; this field is merged in
  `GameObject.printedOrUntilEot`. -/
  untilEotKeywords : Keywords := {}
  /-- This creature loses indestructible until end of turn (e.g. Smite). -/
  untilEotLosesIndestructible : Bool := false
  /-- This permanent loses all abilities until end of turn. -/
  losesAbilitiesUntilEot : Bool := false
  /-- Instances of Iron Fist's granted tap ability this turn (MSH 106). -/
  ironFistTapGrants : Nat := 0
  /-- Triggered abilities granted until end of turn (Lyra, Tolarian
  Archangel). -/
  grantedTriggersUntilEot : Array TriggeredAbility := #[]
  /-- First strike only during its controller's turn, until end of turn. -/
  firstStrikeOnYourTurn : Bool := false
  /-- If this creature would die this turn, exile it instead
  (CR 614.1 / 614.6). -/
  untilEotExileIfDies : Bool := false
  /-- Creatures this player controls cannot block this attacker this turn
  (The Black Gate). Cleared in cleanup. -/
  cantBeBlockedByPlayer : Option PlayerId := none
  /-- Until end of turn, this creature can be blocked only by creatures with
  haste (Speed, Young Avenger). -/
  cantBeBlockedExceptByHasteUntilEot : Bool := false
  /-- This creature can't block this turn. -/
  cantBlockUntilEot : Bool := false
  /-- This permanent dealt damage this turn (Red Guardian; MSH 272). -/
  dealtDamageThisTurn : Bool := false
deriving Repr, Inhabited, BEq

set_option maxHeartbeats 800000 in
/-- Per-turn activation, spell, action, and event tracking state on a permanent
or player (`PlayerTurnState`), reset as a turn ends (CR 119 / CR 504 / CR 508 / CR 514.3 / CR 601.2f / CR 602.5b / CR 603.2 / CR 606.3 / CR 701 / CR 702.111). -/
structure PermanentTurnState where
  /-- Non-mana activations this turn, for “only once each turn”. -/
  activationsThisTurn : Nat := 0
  /-- Indices of activated abilities of this object activated this turn
  (“Activate only once each turn”). -/
  abilitiesActivatedThisTurn : Array Nat := #[]
  /-- A loyalty ability of this permanent was activated this turn (CR 606.3). -/
  loyaltyActivatedThisTurn : Bool := false
  /-- A once-each-turn triggered ability of this permanent has fired. -/
  firedOnceEachTurn : Bool := false
  /-- The optional action of a “Do this only once each turn” trigger has
  been chosen this turn (MSH 69). -/
  optionalOnceUsed : Bool := false
  /-- Alliance modes chosen this turn (0 = add GGG, 1 = +1/+1 each, 2 = scry
  then draw). Reset as the turn ends. -/
  allianceModesChosen : Array Nat := #[]
  /-- A boast ability of this creature has been activated this turn. -/
  boastUsedThisTurn : Bool := false
  /-- Modes of The Vision chosen this turn. Cleared as the turn ends. -/
  modesChosenThisTurn : Array Nat := #[]
  /-- This creature was declared as an attacker this turn (boast, CR 702.111). -/
  declaredAsAttackerThisTurn : Bool := false
  /-- This permanent became tapped this turn (Captain America, Living Legend). -/
  becameTappedThisTurn : Bool := false
  /-- You put a +1/+1 counter on this creature this turn (Kid Loki). -/
  gotPlusOneThisTurn : Bool := false
  /-- This permanent entered the battlefield this turn. -/
  enteredThisTurn : Bool := false
  /-- Players this creature dealt combat damage to this turn (Witch-king of Angmar). -/
  combatDamageToPlayers : Array PlayerId := #[]
  /-- Spells cast this turn (for “second spell each turn” triggers). -/
  spellsCastThisTurn : Nat := 0
  /-- Noncreature spells cast this turn. -/
  noncreatureSpellsCastThisTurn : Nat := 0
  /-- Mana value of each spell this player has cast this turn. -/
  castManaValuesThisTurn : Array Nat := #[]
  /-- Creature spells cast this turn (Radagast of Rhosgobel). -/
  creatureSpellsCastThisTurn : Nat := 0
  /-- Players can't cast spells this turn (Bilbo's Gambit). -/
  cantCastSpellsThisTurn : Bool := false
  /-- Generic mana less to cast spells of each of these types or supertypes this turn
  (CR 601.2f, Armor Wars II). -/
  spellsCostLessThisTurn : Array (SpellCostLess × Nat) := #[]
  /-- Instant or sorcery spells this player casts this turn that are copied
  (Way of the Cryomancer). -/
  copyNextInstantSorceryThisTurn : Nat := 0
  /-- The next spell this player casts this turn can't be countered
  (Theorist's Proxy). -/
  nextSpellCantBeCountered : Bool := false
  /-- Cards drawn this turn (for “second card each turn” triggers). -/
  cardsDrawnThisTurn : Nat := 0
  /-- Cards drawn during your current draw step (Bard, King of Dale). -/
  cardsDrawnThisDrawStep : Nat := 0
  /-- Equip abilities this player activated this turn (Kíli the Resourceful). -/
  equipActivationsThisTurn : Nat := 0
  /-- Times `noteResolveThisTurn` has counted for this player this turn
  (Belladonna Took). -/
  belladonnaResolvesThisTurn : Nat := 0
  /-- Cards discarded this turn (Misty Knight; MSH 375). -/
  cardsDiscardedThisTurn : Nat := 0
  /-- Until end of turn, loyalty abilities of Jace planeswalkers this player
  controls may be activated any time they could cast an instant (Jace's
  Machinations). Each permanent is still limited to one per turn (ruling 766). -/
  jaceLoyaltyAtInstantSpeed : Bool := false
  /-- This player scried this turn (Desperate Futurescribe).
  Scry 0 does not count. -/
  scriedThisTurn : Bool := false
  /-- This player surveilled this turn (Desperate Futurescribe).
  Surveil 0 does not count. -/
  surveilledThisTurn : Bool := false
  /-- This player activated a loyalty ability this turn. -/
  activatedLoyaltyThisTurn : Bool := false
  /-- Cards put into this player's graveyard from their library this turn
  (Cruel Calculations). -/
  cardsMilledThisTurn : Nat := 0
  /-- Until end of turn, each Mountain this player taps for mana adds this
  many additional {R} (Molten Tide). -/
  mountainExtraRedThisTurn : Nat := 0
  /-- A Hero you control entered this turn (Avengers Assemble). -/
  heroEnteredThisTurn : Bool := false
  /-- You attacked with a Hero this turn (Avengers Assemble). -/
  attackedWithHeroThisTurn : Bool := false
  /-- Creatures this player attacked with this turn (Minas Tirith). -/
  creaturesAttackedWithThisTurn : Nat := 0
  /-- Life gained this turn (The Gaffer and similar “if you gained” triggers). -/
  lifeGainedThisTurn : Nat := 0
  /-- Delayed “whenever you attack this turn, pump per Plains” chapters
  still waiting to fire (Roads Go Ever, Ever On). -/
  attackPumpPerPlainsThisTurn : Nat := 0
  /-- An artifact entered under this player's control this turn (Iron Man;
  MSH 242 / 323). Still true if that artifact later left or changed types. -/
  artifactEnteredThisTurn : Bool := false
  /-- This player was dealt noncombat damage this turn (Grim Repriser). -/
  dealtNoncombatDamageThisTurn : Bool := false
  /-- This player was dealt noncombat damage during the previous turn. -/
  dealtNoncombatDamageLastTurn : Bool := false
  /-- Life lost this turn, including from damage (CR 119.3). -/
  lifeLostThisTurn : Nat := 0
  /-- Creatures this player controls can't attack Jace planeswalkers this turn. -/
  cantAttackJaces : Bool := false
deriving Repr, Inhabited, BEq

set_option maxHeartbeats 800000 in
/-- Permanent status (CR 110.5), composed of combat state, counters, until-EOT effects, per-turn tracking, as-enters choices, and lasting effects. -/
structure Status extends
    UntilEotStatus,
    PermanentTurnState where
  /-- +1/+1 counters (CR 122.1). These do not wear off in cleanup. -/
  plusOnePlusOne : Nat := 0
  /-- Minus-one counters (CR 122.1a). -/
  minusOneMinusOne : Nat := 0
  /-- Loyalty counters on a planeswalker (CR 122.1 / 306.5). -/
  loyaltyCounters : Nat := 0
  /-- Charge counters (Gardenize). -/
  charge : Nat := 0
  /-- Stun counters (CR 122.1d). -/
  stun : Nat := 0
  /-- Shield counters. A shield counter is removed instead of taking damage
  or being destroyed (CR 122.1b / Marvel Super Heroes). -/
  shield : Nat := 0
  /-- Finality counters. A permanent with a finality counter that would go
  to a graveyard from the battlefield is exiled instead (MSH release notes). -/
  finality : Nat := 0
  /-- Lore counters on a Saga (CR 714). -/
  lore : Nat := 0
  /-- Time counters (impending, CR 702.176). -/
  time : Nat := 0
  /-- Keyword counters on this permanent (CR 122.1b). -/
  keywordCounters : KeywordCounters := {}
  /-- Hope counters (e.g. Dawn of a New Age). -/
  hope : Nat := 0
  /-- Hone counters. Each grants +1/+0 to the equipped creature while this
  Equipment is attached (judge rulings on Dwalin / Sting). -/
  hone : Nat := 0
  /-- Shadow counters. A permanent with a shadow counter has shadow. -/
  shadow : Nat := 0
  /-- Plan counters on a Plan enchantment. -/
  plan : Nat := 0
  /-- Influence counters (Palantír of Orthanc). -/
  influence : Nat := 0
  /-- Burden counters (The One Ring). -/
  burden : Nat := 0
  /-- Quest counters (Last Light of Durin's Day). -/
  quest : Nat := 0
  /-- Invasion counters (Alien Invasion). -/
  invasion : Nat := 0
  /-- Story counters (Staff of the Storyteller). -/
  story : Nat := 0
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
  /-- Dealt damage by a source with deathtouch since the last time
  state-based actions were checked (CR 704.5h). Cleared after that check. -/
  dealtDeathtouch : Bool := false
  /-- This permanent has dealt combat damage since it entered (Ruric Thar). -/
  dealtCombatDamage : Bool := false
  /-- Modes chosen for the object's lifetime (Gollum, Riddle Master). -/
  chosenModes : Array Nat := #[]
  /-- Odd/even choice (Gollum). `none` until chosen; `some true` is odd. -/
  chosenOdd : Option Bool := none
  /-- Creature type chosen as this permanent entered (Unexpected Party). -/
  chosenCreatureType : Option String := none
  /-- Color chosen as this permanent entered (Room of Refuge). -/
  chosenColor : Option Color := none
  /-- Card name chosen as this permanent entered (Meddling Mage). -/
  chosenName : Option String := none
  /-- Windcrag Siege chose Mardu. Jeskai is `false`. -/
  windcragMardu : Bool := true
  /-- Card type chosen as this permanent entered (Serra's Emissary). -/
  chosenCardType : Option String := none
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
  /-- Sources that stop this permanent becoming untapped while they remain
  (Spider-Woman; Frozen in Ice is attached separately). -/
  cantUntapGrantedBy : Array ObjectId := #[]
  /-- Sources that make this permanent lose its printed abilities while they
  remain (The Wondrous Wasp; MSH 145 / 190). Later granted abilities still
  apply. -/
  losesAbilitiesGrantedBy : Array ObjectId := #[]
  /-- This permanent is only a Food artifact (Supper for Spiders). -/
  onlyFoodArtifact : Bool := false
  /-- This permanent is an artifact and not a creature (Tom, Bert, and William). -/
  returnedAsArtifact : Bool := false
  /-- An attached Aura makes this a 5/5 Construct creature in addition to its
  other types (Puppet Crafting). Refreshed with state-based actions. -/
  animatedConstruct55 : Bool := false
  /-- This permanent is not a creature (impending, until the last time counter). -/
  notACreature : Bool := false
  /-- Until end of turn, combat damage to a player creates a Treasure. -/
  combatDamageCreatesTreasure : Bool := false
  /-- A control-changing effect lasts until end of turn (Act of Treason,
  Sauron, the Lidless Eye). Cleared in cleanup; ending it may exile (CR 800.4c). -/
  controlUntilEot : Bool := false
  /-- Endings of this object's controller's turns before control reverts
  (Evil's Thrall: 2 means until the end of your next turn). -/
  controlTurnEndsLeft : Nat := 0
  /-- +P/+T lasting until the listed player's next turn begins (Garruk,
  Veiled Butcher). -/
  untilTurnOfPump : Array (PlayerId × Int × Int) := #[]
  /-- This land has “{T}: Add {C}{C}” until the exiled card with this id is
  cast from exile (Emrakul, the Exigent Doom; rulings 729 / 730). -/
  colorlessGrantUntilCast : Array ObjectId := #[]
  /-- Goaded for as long as this flag remains (CR 701.38). -/
  goaded : Bool := false
  /-- This card may be cast from its owner's graveyard without paying its
  mana cost, ignoring timing, until end of turn. -/
  freeCastFromGraveyard : Bool := false
  /-- Phased out (CR 702.26). Treated as though it does not exist. -/
  phasedOut : Bool := false
  /-- Host this Aura or Equipment phased out with. -/
  phasedWith : Option ObjectId := none
  /-- This creature is its controller's Ring-bearer. -/
  ringBearer : Bool := false
  /-- A power-up ability of this permanent has been activated (CR 702.193). -/
  powerUpUsed : Bool := false
  /-- How many times a power-up ability of this permanent has been activated.
  Wonder Man raises the lifetime limit above one (MSH). -/
  powerUpActivations : Nat := 0
  /-- The Mind Stone (or similar) has been harnessed. -/
  harnessed : Bool := false
  /-- This permanent is currently showing its back face (MSH modal DFC). -/
  transformed : Bool := false
  /-- Entered back-face-up because it is night and the front has daybound
  (MSH 191). Transform is illegal. -/
  cantTransform : Bool := false
  /-- Mana spent to cast this spell (CR 601.2h). -/
  manaSpentToCast : Nat := 0
  /-- An exhaust ability of this permanent has been activated (CR 702.177). -/
  exhaustUsed : Bool := false
  /-- Face down (morph, CR 702.37). A 2/2 creature with no abilities. -/
  faceDown : Bool := false
  tapped : Bool := false
  damage : Int := 0
  summoningSick : Bool := true
  /-- This permanent is prepared (Reality Fracture). -/
  prepared : Bool := false
  /-- This permanent is a commander. -/
  isCommander : Bool := false
deriving Repr, Inhabited

namespace Status

/-- Until-end-of-turn power bonus. -/
def pumpPower (s : Status) : Int := s.pump.1

/-- Until-end-of-turn toughness bonus. -/
def pumpToughness (s : Status) : Int := s.pump.2

/-- Until-end-of-turn layer-7b base power, if set. -/
def setBasePower (s : Status) : Option Int := s.setBasePT.map (·.1)

/-- Until-end-of-turn layer-7b base toughness, if set. -/
def setBaseToughness (s : Status) : Option Int := s.setBasePT.map (·.2)

/-- Mark `n` damage on this permanent (CR 120). `deathtouch` records that a
source with deathtouch dealt this damage (CR 702.2 / 704.5h). -/
def addDamage (s : Status) (n : Int) (deathtouch := false) : Status :=
  { s with
    damage := s.damage + n
    dealtDeathtouch := s.dealtDeathtouch || (deathtouch && n > 0) }

/-- Trample counters on this permanent (CR 122.1b). -/
abbrev trampleCounters (s : Status) : Nat := s.keywordCounters.trample

/-- Indestructible counters on this permanent (CR 122.1b). -/
abbrev indestructibleCounters (s : Status) : Nat := s.keywordCounters.indestructible

/-- Lifelink counters on this permanent (CR 122.1b). -/
abbrev lifelinkCounters (s : Status) : Nat := s.keywordCounters.lifelink

/-- Number of counters of `kind` on this permanent (CR 122.1). -/
def counter (s : Status) : CounterKind → Nat
  | .plusOnePlusOne => s.plusOnePlusOne
  | .minusOneMinusOne => s.minusOneMinusOne
  | .loyalty => s.loyaltyCounters
  | .hope => s.hope
  | .charge => s.charge
  | .stun => s.stun
  | .shield => s.shield
  | .finality => s.finality
  | .plan => s.plan
  | .burden => s.burden
  | .quest => s.quest
  | .invasion => s.invasion
  | .influence => s.influence
  | .trample => s.keywordCounters.trample
  | .indestructible => s.keywordCounters.indestructible
  | .lifelink => s.keywordCounters.lifelink
  | .hone => s.hone
  | .shadow => s.shadow
  | .lore => s.lore
  | .story => s.story
  | .time => s.time
  | .haste => s.keywordCounters.haste
  | .vigilance => s.keywordCounters.vigilance
  | .flying => s.keywordCounters.flying
  | .menace => s.keywordCounters.menace
  | .reach => s.keywordCounters.reach
  | .deathtouch => s.keywordCounters.deathtouch
  | .firstStrike => s.keywordCounters.firstStrike
  | _ => s.keywordCounters.doubleStrike

/-- Set the count of `kind` counters on this permanent (CR 122.1). -/
def setCounter (s : Status) (kind : CounterKind) (n : Nat) : Status :=
  match kind with
  | .plusOnePlusOne => { s with plusOnePlusOne := n }
  | .minusOneMinusOne => { s with minusOneMinusOne := n }
  | .loyalty => { s with loyaltyCounters := n }
  | .hope => { s with hope := n }
  | .charge => { s with charge := n }
  | .stun => { s with stun := n }
  | .shield => { s with shield := n }
  | .finality => { s with finality := n }
  | .plan => { s with plan := n }
  | .burden => { s with burden := n }
  | .quest => { s with quest := n }
  | .invasion => { s with invasion := n }
  | .influence => { s with influence := n }
  | .trample => { s with keywordCounters := { s.keywordCounters with trample := n } }
  | .indestructible => { s with keywordCounters := { s.keywordCounters with indestructible := n } }
  | .lifelink => { s with keywordCounters := { s.keywordCounters with lifelink := n } }
  | .hone => { s with hone := n }
  | .shadow => { s with shadow := n }
  | .lore => { s with lore := n }
  | .story => { s with story := n }
  | .time => { s with time := n }
  | .haste => { s with keywordCounters := { s.keywordCounters with haste := n } }
  | .vigilance => { s with keywordCounters := { s.keywordCounters with vigilance := n } }
  | .flying => { s with keywordCounters := { s.keywordCounters with flying := n } }
  | .menace => { s with keywordCounters := { s.keywordCounters with menace := n } }
  | .reach => { s with keywordCounters := { s.keywordCounters with reach := n } }
  | .deathtouch => { s with keywordCounters := { s.keywordCounters with deathtouch := n } }
  | .firstStrike => { s with keywordCounters := { s.keywordCounters with firstStrike := n } }
  | _ => { s with keywordCounters := { s.keywordCounters with doubleStrike := n } }

/-- True when this permanent has a counter (CR 122.1). -/
def hasCounters (s : Status) : Bool :=
  CounterKind.all.any (fun k => s.counter k > 0)

/-- This permanent with every counter removed. -/
def withoutCounters (s : Status) : Status :=
  CounterKind.all.foldl (fun acc k => acc.setCounter k 0) s

/-- Another counter of each kind already on this permanent (CR 701.34a).
+1/+1 counters are added by the caller so their triggers apply. -/
def proliferatedExceptPlusOne (s : Status) (extra : Nat := 0) : Status :=
  CounterKind.all.foldl (fun acc k =>
    if k == .plusOnePlusOne || acc.counter k == 0 then acc
    else acc.setCounter k (acc.counter k + 1 + extra)) s

/-- Put the same number of each kind of counter `from` has, except +1/+1
counters, which the caller adds so their triggers apply (Graft Surgeon). -/
def addCountersExceptPlusOne (s «from» : Status) (extra : Nat := 0) : Status :=
  CounterKind.all.foldl (fun acc k =>
    let n := «from».counter k
    if k == .plusOnePlusOne || n == 0 then acc
    else acc.setCounter k (acc.counter k + n + extra)) s

/-- Until-end-of-turn +P/+T (CR 613.4c / 611.2a). -/
def addPump (s : Status) (p t : Int) : Status :=
  { s with pump := (s.pump.1 + p, s.pump.2 + t) }

/-- Put `n` +1/+1 counters on this permanent (CR 122.1). -/
def addPlusOnePlusOne (s : Status) (n : Nat := 1) : Status :=
  { s with plusOnePlusOne := s.plusOnePlusOne + n }

/-- Put `n` counters of `kind` on this permanent (CR 122.1). -/
def addCounters (s : Status) (kind : CounterKind) (n : Nat) : Status :=
  let s' := s.setCounter kind (s.counter kind + n)
  if kind == .plusOnePlusOne then
    { s' with gotPlusOneThisTurn := s'.gotPlusOneThisTurn || n > 0 }
  else s'

/-- Union printed-style keyword grants that last until end of turn. -/
def grantUntilEot (s : Status) (k : Keywords) : Status :=
  { s with untilEotKeywords := Keywords.merge s.untilEotKeywords k }

/-- True when cleanup must clear until-EOT pumps, damage, keyword grants, or
base P/T setting (CR 514.3). -/
def clearsAtCleanup (s : Status) : Bool :=
  s.damage != 0 || s.toUntilEotStatus != {}

/-- Status after the cleanup step removes until-EOT effects (CR 514.3). -/
def clearedAtCleanup (s : Status) : Status :=
  { s with damage := 0, toUntilEotStatus := {} }

/-- True when this permanent has per-turn activation or event tracking state to
reset as a turn ends. -/
def hasTurnStateToClear (s : Status) : Bool :=
  s.toPermanentTurnState != {}

/-- Status with per-turn activation and event tracking fields reset as a turn ends. -/
def clearedAtEndOfTurn (s : Status) : Status :=
  { s with toPermanentTurnState := {} }

end Status

#guard
  let s : Status := { pump := (1, 2), damage := 3, setBasePT := some (4, 4) }
  s.clearsAtCleanup && s.pumpPower == 1 && s.pumpToughness == 2 &&
    s.setBasePower == some 4 &&
    s.clearedAtCleanup.pump == (0, 0) && s.clearedAtCleanup.damage == 0 &&
    s.clearedAtCleanup.setBasePT.isNone
#guard !({} : Status).clearsAtCleanup

end Mtg.Engine
