import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.TriggerEvent
import Mtg.Engine.Turn
import Mtg.Engine.TypeLine
import Mtg.Engine.Zone

/-!
# Game events (CR 603.2 / 614.1)

Every change to the game state is one `GameEvent`. The log on `Game` is
those changes, oldest first, for the whole game. A condition asks the log
whether an action happened. A triggered ability matches the change that
happened. A replacement effect matches the change that would happen, before
it is recorded; a replaced change is not recorded (CR 614.6).
-/

namespace Mtg.Engine

/-- The object a `GameEvent` is about, as it existed when the change happened
(CR 113.7a). Subtypes include those granted at that moment. -/
structure EventObject where
  id : ObjectId
  controller : Option PlayerId := none
  owner : PlayerId := ⟨0⟩
  creature : Bool := false
  token : Bool := false
  artifact : Bool := false
  land : Bool := false
  planeswalker : Bool := false
  instantOrSorcery : Bool := false
  equipment : Bool := false
  legendary : Bool := false
  attacking : Bool := false
  changeling : Bool := false
  subtypes : Array String := #[]
deriving Repr, Inhabited, BEq

namespace EventObject

/-- `s` is one of this object's types, including changeling creature types
(CR 702.72). -/
def hasSubtype (o : EventObject) (s : String) : Bool :=
  o.subtypes.any (· == s) || (o.changeling && !isNoncreatureSubtype s)

/-- Goblin, Orc, or Army. -/
def goblinOrcArmy (o : EventObject) : Bool :=
  o.hasSubtype "Goblin" || o.hasSubtype "Orc" || o.hasSubtype "Army"

/-- Villain. -/
def villain (o : EventObject) : Bool :=
  o.hasSubtype "Villain"

/-- Hero. -/
def hero (o : EventObject) : Bool :=
  o.hasSubtype "Hero"

/-- Elf. -/
def elf (o : EventObject) : Bool :=
  o.hasSubtype "Elf"

/-- Merfolk. -/
def merfolk (o : EventObject) : Bool :=
  o.hasSubtype "Merfolk"

/-- Forest. -/
def forest (o : EventObject) : Bool :=
  o.hasSubtype "Forest" || (o.land && o.subtypes.any (· == "Forest"))

/-- Mountain. -/
def mountain (o : EventObject) : Bool :=
  o.hasSubtype "Mountain"

end EventObject

/-- One change to the game, without the turn number. `GameEvent` stores the turn. -/
inductive GameChange where
  /-- `object` moved from `fromZone` to `toZone`.
  A creature moving from the battlefield to a graveyard died (CR 700.4).
  A card moving from its owner's hand to that player's graveyard was
  discarded when `discarded`. `sacrificed` is set when the move was a
  sacrifice that was not replaced. -/
  | moved (object : EventObject) (fromZone toZone : Zone)
      (sacrificed discarded : Bool := false)
  /-- `player` drew `card`. `nth` is how many cards that player has drawn
  this turn, including this one. `firstOfOwnDrawStep` is the first card of
  that player's own draw step (CR 121.2). -/
  | drew (player : PlayerId) (card : ObjectId) (nth : Nat) (firstOfOwnDrawStep : Bool)
  /-- `player` gained or lost `amount` life. Gaining is `gained`.
  Life lost because of damage has `fromDamage`. Combat damage has `combat`. -/
  | life (player : PlayerId) (amount : Nat) (gained fromDamage combat : Bool := false)
  /-- `amount` damage was dealt to `object`. `combat` is combat damage. -/
  | damaged (source : Option ObjectId) (object : EventObject) (amount : Nat) (combat : Bool)
  /-- `amount` damage was dealt to `player`. -/
  | damagedPlayer (source : Option ObjectId) (player : PlayerId) (amount : Nat) (combat : Bool)
  /-- `player` cast `spell` from `fromZone`. `manaSpent` is the mana paid. -/
  | cast (player : PlayerId) (spell : EventObject) (fromZone : Zone)
      (manaValue manaSpent : Nat) (fromGraveyard teamwork gift : Bool := false)
  /-- `player` attacked with `attacker`. -/
  | attacked (player : PlayerId) (attacker : EventObject) (whom : PlayerId)
  /-- `object` became tapped (`nowTapped`) or the tap was the change.
  `duringControllersTurn` is true on that object's controller's turn. -/
  | tapped (object : EventObject) (nowTapped duringControllersTurn : Bool)
  /-- `n` counters of `kind` were put on or removed from `object`.
  `removed` is a removal. -/
  | counters (player : Option PlayerId) (object : EventObject) (kind : CounterKind)
      (n : Nat) (removed : Bool := false)
  /-- `player` looked at `n` cards by scrying, or by surveilling when `surveil`.
  `asked` is the printed number. Scry 0 is not recorded. Scrying a positive
  number still happens when the library has fewer cards (CR 701.20). -/
  | looked (player : PlayerId) (n : Nat) (surveil : Bool := false) (asked : Nat := n)
  /-- `player` sacrificed `object`, and the sacrifice was not replaced. -/
  | sacrificed (player : PlayerId) (object : EventObject)
  /-- `player` created `object`. -/
  | created (player : PlayerId) (object : EventObject)
  /-- `object` changed controller from `fromPlayer` to `toPlayer`. -/
  | control (object : ObjectId) (fromPlayer toPlayer : PlayerId)
  /-- The game entered `step` on `active`'s turn. A skipped step is not recorded
  (CR 614.10). -/
  | stepped (step : Step) (active : PlayerId)
  /-- `player` activated an ability of `source`. `loyalty` is a loyalty ability.
  `equip` is an equip ability, recorded when the activation is completed. -/
  | activated (player : PlayerId) (source : EventObject) (loyalty equip : Bool)
  /-- `player` spent `amount` mana. -/
  | spentMana (player : PlayerId) (amount : Nat)
  /-- `player` played `land` as a land drop (CR 305.1). Putting a land onto
  the battlefield another way is not a play. -/
  | playedLand (player : PlayerId) (land : EventObject)
  /-- The `nth` time `player` resolved the ability that counts its own
  resolutions this turn. -/
  | resolved (player : PlayerId) (nth : Nat)
  /-- `object` became attached to `host`. -/
  | attached (object host : ObjectId)
  /-- `player` beheld `quality`. Later zone changes do not undo it. -/
  | beheld (player : PlayerId) (quality : String)
  /-- `player` got `n` poison counters. -/
  | poisoned (player : PlayerId) (n : Nat)
  /-- `player` proliferated. -/
  | proliferated (player : PlayerId)
  /-- `player` chose to have The Sensational She-Hulk deal damage. Once each turn. -/
  | sheHulkDealtDamage (player : PlayerId)
  /-- `object` untapped. `replacedByStun` means a stun counter was removed
  instead, so the untap did not happen (CR 122.1d). -/
  | untapped (object : EventObject) (replacedByStun : Bool := false)
deriving Repr, Inhabited, BEq

/-- A game state change on a given turn (CR 500). `Game.events` records each
one that happens. -/
structure GameEvent where
  turn : Nat
  change : GameChange
deriving Repr, Inhabited, BEq

namespace GameEvent

/-- `object` moved from `fromZone` to `toZone`. -/
def moved (turn : Nat) (object : EventObject) (fromZone toZone : Zone)
    (sacrificed : Bool := false) (discarded : Bool := false) : GameEvent :=
  ⟨turn, .moved object fromZone toZone sacrificed discarded⟩

/-- `player` drew `card` as the `nth` card this turn. -/
def drew (turn : Nat) (player : PlayerId) (card : ObjectId) (nth : Nat)
    (firstOfOwnDrawStep : Bool := false) : GameEvent :=
  ⟨turn, .drew player card nth firstOfOwnDrawStep⟩

/-- `player` gained or lost life. -/
def life (turn : Nat) (player : PlayerId) (amount : Nat)
    (gained : Bool := false) (fromDamage : Bool := false) (combat : Bool := false) : GameEvent :=
  ⟨turn, .life player amount gained fromDamage combat⟩

/-- Damage was dealt to an object. -/
def damaged (turn : Nat) (source : Option ObjectId) (object : EventObject)
    (amount : Nat) (combat : Bool := false) : GameEvent :=
  ⟨turn, .damaged source object amount combat⟩

/-- Damage was dealt to a player. -/
def damagedPlayer (turn : Nat) (source : Option ObjectId) (player : PlayerId)
    (amount : Nat) (combat : Bool := false) : GameEvent :=
  ⟨turn, .damagedPlayer source player amount combat⟩

/-- `player` cast `spell`. -/
def cast (turn : Nat) (player : PlayerId) (spell : EventObject) (fromZone : Zone)
    (manaValue : Nat := 0) (manaSpent : Nat := 0)
    (fromGraveyard : Bool := false) (teamwork : Bool := false) (gift : Bool := false) : GameEvent :=
  ⟨turn, .cast player spell fromZone manaValue manaSpent fromGraveyard teamwork gift⟩

/-- `player` attacked `whom` with `attacker`. -/
def attacked (turn : Nat) (player : PlayerId) (attacker : EventObject) (whom : PlayerId) : GameEvent :=
  ⟨turn, .attacked player attacker whom⟩

/-- `object` became tapped or untapped by a tap action. `nowTapped` is the result. -/
def tapped (turn : Nat) (object : EventObject) (nowTapped : Bool)
    (duringControllersTurn : Bool := false) : GameEvent :=
  ⟨turn, .tapped object nowTapped duringControllersTurn⟩

/-- Counters were put on or removed from `object`. -/
def counters (turn : Nat) (player : Option PlayerId) (object : EventObject)
    (kind : CounterKind) (n : Nat) (removed : Bool := false) : GameEvent :=
  ⟨turn, .counters player object kind n removed⟩

/-- `player` scried or surveilled. `n` cards were looked at. `asked` is the
printed number; it defaults to `n`. -/
def looked (turn : Nat) (player : PlayerId) (n : Nat) (surveil : Bool := false)
    (asked : Nat := n) : GameEvent :=
  ⟨turn, .looked player n surveil asked⟩

/-- `player` sacrificed `object`. -/
def sacrificed (turn : Nat) (player : PlayerId) (object : EventObject) : GameEvent :=
  ⟨turn, .sacrificed player object⟩

/-- `player` created `object`. -/
def created (turn : Nat) (player : PlayerId) (object : EventObject) : GameEvent :=
  ⟨turn, .created player object⟩

/-- The step or phase changed. -/
def stepped (turn : Nat) (step : Step) (active : PlayerId) : GameEvent :=
  ⟨turn, .stepped step active⟩

/-- `player` activated an ability of `source`. `equip` is set when the
activation has been completed, so a proposal still being paid does not count. -/
def activated (turn : Nat) (player : PlayerId) (source : EventObject)
    (loyalty : Bool := false) (equip : Bool := false) : GameEvent :=
  ⟨turn, .activated player source loyalty equip⟩

/-- `player` played `land`. -/
def playedLand (turn : Nat) (player : PlayerId) (land : EventObject) : GameEvent :=
  ⟨turn, .playedLand player land⟩

/-- The `nth` counted resolution for `player` this turn. -/
def resolved (turn : Nat) (player : PlayerId) (nth : Nat) : GameEvent :=
  ⟨turn, .resolved player nth⟩

/-- `player` spent mana. -/
def spentMana (turn : Nat) (player : PlayerId) (amount : Nat) : GameEvent :=
  ⟨turn, .spentMana player amount⟩

/-- `player` got poison counters. -/
def poisoned (turn : Nat) (player : PlayerId) (n : Nat) : GameEvent :=
  ⟨turn, .poisoned player n⟩

/-- `player` proliferated. -/
def proliferated (turn : Nat) (player : PlayerId) : GameEvent :=
  ⟨turn, .proliferated player⟩

/-- `player` chose to have The Sensational She-Hulk deal damage. -/
def sheHulkDealtDamage (turn : Nat) (player : PlayerId) : GameEvent :=
  ⟨turn, .sheHulkDealtDamage player⟩

/-- `object` untapped, or a stun counter replaced that untap. -/
def untapped (turn : Nat) (object : EventObject) (replacedByStun : Bool := false) : GameEvent :=
  ⟨turn, .untapped object replacedByStun⟩

/-- Same event, sent to `toZone` instead. Used after a zone replacement. -/
def withDestination (e : GameEvent) (toZone : Zone) (discarded : Bool) : GameEvent :=
  match e.change with
  | .moved object fromZone _ sacrificed _ =>
    ⟨e.turn, .moved object fromZone toZone sacrificed discarded⟩
  | _ => e

/-- A creature moved from the battlefield to a graveyard (CR 700.4). -/
def isCreatureToGraveyard (e : GameEvent) : Bool :=
  match e.change with
  | .moved object .battlefield (.graveyard _) _ _ => object.creature
  | _ => false

/-- A permanent moved from the battlefield to a graveyard. -/
def isPermanentToGraveyard (e : GameEvent) : Bool :=
  match e.change with
  | .moved _ .battlefield (.graveyard _) _ _ => true
  | _ => false

/-- An object left the stack for another zone. -/
def leavesStack (e : GameEvent) : Bool :=
  match e.change with
  | .moved _ .stack toZone _ _ => toZone != .stack
  | _ => false

/-- An instant or sorcery moved from the stack to its owner's graveyard. -/
def entersOwnGraveyardFromStack (e : GameEvent) : Bool :=
  match e.change with
  | .moved object .stack (.graveyard owner) _ _ =>
    object.instantOrSorcery && owner == object.owner
  | _ => false

/-- A permanent entered the battlefield. -/
def enteredBattlefield (e : GameEvent) : Bool :=
  match e.change with
  | .moved _ _ .battlefield _ _ => true
  | _ => false

/-- The kind of event a replacement effect watches (CR 614.1). -/
inductive ReplacementWatch where
  /-- A creature would die. -/
  | wouldDie
  /-- A permanent would move from the battlefield to a graveyard. -/
  | wouldEnterGraveyardFromBattlefield
  /-- An object would leave the stack. -/
  | wouldLeaveStack
  /-- An instant or sorcery would go from the stack to its owner's graveyard. -/
  | wouldEnterGraveyardFromStack
  /-- A player would draw a card. -/
  | wouldDraw
  /-- A player would gain life. -/
  | wouldGainLife
  /-- Damage would be dealt. -/
  | wouldDealDamage
  /-- A permanent would enter the battlefield. -/
  | wouldEnterBattlefield
  /-- A token would be created. -/
  | wouldCreateToken
  /-- Counters would be put on an object. -/
  | wouldPutCounter
  /-- A permanent would untap. -/
  | wouldUntap
deriving Repr, Inhabited, BEq, DecidableEq

/-- Whether this change is one `watch` replaces or modifies. -/
def watches (e : GameEvent) (watch : ReplacementWatch) : Bool :=
  match watch with
  | .wouldDie => e.isCreatureToGraveyard
  | .wouldEnterGraveyardFromBattlefield => e.isPermanentToGraveyard
  | .wouldLeaveStack => e.leavesStack
  | .wouldEnterGraveyardFromStack => e.entersOwnGraveyardFromStack
  | .wouldDraw =>
    match e.change with
    | .drew _ _ _ _ => true
    | _ => false
  | .wouldGainLife =>
    match e.change with
    | .life _ _ true _ _ => true
    | _ => false
  | .wouldDealDamage =>
    match e.change with
    | .damaged _ _ _ _ | .damagedPlayer _ _ _ _ => true
    | _ => false
  | .wouldEnterBattlefield => e.enteredBattlefield
  | .wouldCreateToken =>
    match e.change with
    | .created _ _ => true
    | _ => false
  | .wouldPutCounter =>
    match e.change with
    | .counters _ _ _ n false => n > 0
    | _ => false
  | .wouldUntap =>
    match e.change with
    | .untapped _ false => true
    | _ => false

/-- `listener`'s ability on `sourceId` triggers from this change.
“This” abilities require `sourceId` to be the object that changed.
“You” abilities require `listener` to be the player who did it.
An event this change does not describe does not match. -/
def matchesTrigger (e : GameEvent) (listener : PlayerId) (sourceId : ObjectId)
    (te : TriggerEvent) : Bool :=
  let you (p : PlayerId) : Bool := p == listener
  let this (o : EventObject) : Bool := o.id == sourceId
  let yours (o : EventObject) : Bool := o.controller == some listener
  let other (o : EventObject) : Bool := o.id != sourceId
  match e.change, te with
  | .drew p _ _ _, .youDraw => you p
  | .drew p _ nth _, .youDrawSecondCard => you p && nth == 2
  | .drew _ _ nth _, .anyPlayerDrawsSecond => nth == 2
  | .drew p _ _ first, .opponentDrawsExceptFirstDrawStep => !you p && !first
  | .drew p _ nth _, .opponentDrawsSecondCard => !you p && nth == 2
  | .life p _ true _ _, .youGainLife => you p
  | .life _ _ false _ _, .playerLosesLife => true
  | .damaged _ object _ _, .sourceDealtDamage => this object
  | .damaged _ object _ false, .sourceDealtNoncombatDamage => this object
  | .damaged _ object _ _, .creatureYouControlDealtDamage =>
    yours object && object.creature
  | .damagedPlayer _ _ _ true, .dealsCombatDamageToPlayer => true
  | .damagedPlayer _ _ _ true, .dealsCombatDamageToPlayerOrBattle => true
  | .damagedPlayer _ p _ true, .combatDamageToYou => you p
  | .damaged _ object _ _, .heroesDealDamageToPlayer =>
    yours object && object.hero
  | .moved object .battlefield (.graveyard _) _ _, .dying =>
    this object && object.creature
  | .moved object .battlefield _ _ _, .leaving => this object
  | .moved object _ .battlefield _ _, .entering => this object
  | .moved object _ .battlefield _ _, .landYouControlEnters =>
    yours object && object.land
  | .moved object _ .battlefield _ _, .forestYouControlEnters =>
    yours object && object.forest
  | .moved object _ .battlefield _ _, .mountainYouControlEnters =>
    yours object && object.mountain
  | .moved object _ .battlefield _ _, .artifactYouControlEnters =>
    yours object && object.artifact
  | .moved object _ .battlefield _ _, .creatureYouControlEnters =>
    yours object && object.creature
  | .moved object _ .battlefield _ _, .anotherCreatureYouControlEnters =>
    yours object && other object && object.creature
  | .moved object _ .battlefield _ _, .anotherElfYouControlEnters =>
    yours object && other object && object.elf
  | .moved object _ .battlefield _ _, .tokenYouControlEnters =>
    yours object && object.token
  | .moved object _ .battlefield _ _, .equipmentYouControlEnters =>
    yours object && object.equipment
  | .moved object _ .battlefield _ _, .anotherArtifactEnters =>
    yours object && other object && object.artifact
  | .moved object _ .battlefield _ _, .anotherVillainEnters =>
    yours object && other object && object.villain
  | .moved object _ .battlefield _ _, .anotherVillainOrArtifactEnters =>
    yours object && other object && (object.villain || object.artifact)
  | .moved object _ .battlefield _ _, .anotherNontokenHeroEnters =>
    yours object && other object && !object.token && object.hero
  | .moved object _ .battlefield _ _, .anotherNontokenArtifactEnters =>
    yours object && other object && !object.token && object.artifact
  | .moved object .battlefield (.graveyard _) _ _, .creatureYouControlDies =>
    yours object && object.creature
  | .moved object .battlefield (.graveyard _) _ _, .nontokenYouControlDies =>
    yours object && object.creature && !object.token
  | .moved object .battlefield (.graveyard _) _ _, .anotherGoblinOrcArmyDies =>
    yours object && other object && object.creature && object.goblinOrcArmy
  | .moved object .battlefield (.graveyard _) _ _, .villainYouControlDies =>
    yours object && other object && object.creature && object.villain
  | .moved object .battlefield (.graveyard _) _ _, .attackingCreatureYouControlDies =>
    yours object && object.creature && object.attacking
  | .moved object .battlefield (.graveyard _) _ _, .oneOrMoreOtherCreaturesDie =>
    other object && object.creature
  | .moved object .battlefield (.hand _) _ _, .anotherNonlandReturned =>
    yours object && other object && !object.land
  | .moved object (.graveyard owner) _ _ _, .creatureCardLeavesYourGy =>
    you owner && object.creature
  | .moved object _ (.graveyard owner) _ _, .creatureCardsPutIntoYourGy =>
    you owner && object.creature && !object.token
  | .moved _ (.hand p) (.graveyard q) _ true, .youDiscard =>
    you p && p == q
  | .moved object (.hand p) (.graveyard q) _ true, .fra .youDiscardThis =>
    you p && p == q && this object
  | .moved _ (.hand p) (.graveyard q) _ true, .fra .youDiscardOne =>
    you p && p == q
  | .moved _ (.hand p) (.graveyard q) _ true, .fra .playerDiscards =>
    p == q
  | .moved object .battlefield (.graveyard _) _ _, .fra .enchantedDies =>
    object.creature
  | .moved object .battlefield (.graveyard _) _ _, .fra .nontokenCreatureYouControlDies =>
    yours object && object.creature && !object.token
  | .moved object .battlefield (.graveyard _) _ _, .fra .anotherCreatureOrPlaneswalkerYouControlDies =>
    yours object && other object && (object.creature || object.planeswalker)
  | .moved object .battlefield _ _ _, .fra .creatureYouControlLeaves =>
    yours object && other object && object.creature
  | .moved object _ .battlefield _ _, .subtypeYouControlEnters _ =>
    yours object
  | .cast p spell _ _ _ _ _ _, .youCastInstantOrSorcery =>
    you p && spell.instantOrSorcery
  | .cast p spell _ _ _ _ _ _, .youCastNoncreature =>
    you p && !spell.creature
  | .cast p spell _ _ _ _ _ _, .youCastCreature =>
    you p && spell.creature
  | .cast p _ _ _ _ _ _ _, .youCastSpell => you p
  | .cast p _ _ _ _ _ _ _, .youCastColor _ => you p
  | .cast p _ (.hand _) _ _ _ _ _, .youCastColorFromHand _ => you p
  | .cast p _ _ _ _ _ _ _, .youCastGreen => you p
  | .cast p spell _ _ _ _ _ _, .youCastVillain => you p && spell.villain
  | .cast p _ _ _ _ _ _ _, .opponentCastsSpell => !you p
  | .cast p spell _ _ _ _ _ _, .youCastFirstNoncreature => you p && !spell.creature
  | .cast p _ _ _ _ _ _ _, .youCastSecondSpell => you p
  | .cast _ _ _ _ _ _ _ _, .anyPlayerCastsSecondSpell => true
  | .cast p _ _ _ _ _ _ _, .opponentCastsFirstNoncreature => !you p
  | .cast p spell _ _ _ _ _ _, .fra .castThis => you p && this spell
  | .attacked p attacker _, .attacking => you p && this attacker
  | .attacked p _ _, .youAttack => you p
  | .attacked p attacker _, .youAttackWithElves => you p && attacker.elf
  | .attacked p _ _, .youAttackWithTwoOrMore => you p
  | .attacked p attacker _, .creatureYouControlAttacksAlone =>
    you p && attacker.creature
  | .attacked p _ _, .equippedAttacks => you p
  | .attacked p attacker _, .equippedCreatureYouControlAttacks =>
    you p && attacker.creature
  | .attacked p attacker _, .merfolkAttackPlayer => you p && attacker.merfolk
  | .attacked p attacker _, .fra .creatureYouControlAttacks =>
    you p && attacker.creature
  | .tapped object true _, .sourceBecomesTapped => this object
  | .tapped object true _, .creaturesYouControlBecomeTapped =>
    yours object && object.creature
  | .tapped object true _, .equippedBecomesTapped => object.creature
  | .tapped object true during, .creatureYouControlTapped =>
    yours object && object.creature && during
  | .looked p _ false asked, .youScry => you p && asked > 0
  | .looked p _ _ asked, .youScryOrSurveil => you p && asked > 0
  | .counters (some p) _ .plusOnePlusOne n false, .youPutPlusOne =>
    you p && n > 0
  | .counters (some p) object _ n false, .youPutCountersOnGoblinOrcArmy =>
    you p && n > 0 && object.goblinOrcArmy
  | .counters _ object .plan n false, .nthPlanCounter _ =>
    this object && n > 0
  | .counters _ object .lore n false, .sagaChapter =>
    this object && n > 0
  | .stepped .upkeep active, .yourUpkeep => you active
  | .stepped .upkeep _, .eachUpkeep => true
  | .stepped .upkeep _, .fra .eachUpkeepFromGraveyard => true
  | .stepped .end active, .yourEndStep => you active
  | .stepped .end _, .eachEndStep => true
  | .stepped .beginningOfCombat active, .yourBeginCombat => you active
  | .stepped .beginningOfCombat active, .fra .yourBeginCombatFromGraveyard => you active
  | .stepped .beginningOfCombat _, .eachBeginCombat => true
  | .stepped .beginningOfCombat active, .fra .opponentBeginCombat => !you active
  | .stepped .precombatMain active, .yourFirstMain => you active
  | .stepped .draw active, .eachOpponentDrawStep => !you active
  | .stepped .upkeep _, .eaglesCreateBirds => true
  | .stepped .upkeep active, .enchantedControllerUpkeep => you active
  | .sacrificed p object, .youSacrificeToken => you p && object.token
  | .activated p _ true _, .youActivateLoyaltyAbility => you p
  | .activated p source false _, .youActivateCreatureAbility =>
    you p && source.creature
  | .activated p _ true _, .fra .opponentActivatesLoyaltyAbility => !you p
  | .created p object, .fra .youCreateCreatureTokens => you p && object.creature
  | _, _ => false

/-- Cards `p` drew on `turn` in `events`. -/
def draws (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .drew q _ _ _ => if q == p then n + 1 else n
      | _ => n) 0

/-- Life `p` gained on `turn`. -/
def lifeGained (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .life q amount true _ _ => if q == p then n + amount else n
      | _ => n) 0

/-- Creatures that died on `turn`. -/
def creatureDeaths (events : Array GameEvent) (turn : Nat) : Nat :=
  events.foldl (fun n e =>
    if e.turn == turn && e.isCreatureToGraveyard then n + 1 else n) 0

/-- Spells `p` cast on `turn`. -/
def spellsCast (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .cast q _ _ _ _ _ _ _ => if q == p then n + 1 else n
      | _ => n) 0

/-- `p` scried at least one card on `turn`. -/
def scried (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .looked q _ false asked => q == p && asked > 0
      | _ => false

/-- `p` surveilled on `turn`. Surveil 0 does not count. -/
def surveilled (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .looked q _ true asked => q == p && asked > 0
      | _ => false

/-- An artifact entered under `p`'s control on `turn`. -/
def artifactEntered (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .moved object _ .battlefield _ _ =>
        object.controller == some p && object.artifact
      | .created q object => q == p && object.artifact
      | _ => false

/-- `p` attacked with a permanent of `subtype` on `turn`. -/
def attackedWithSubtype (events : Array GameEvent) (turn : Nat) (p : PlayerId)
    (subtype : String) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .attacked q attacker _ => q == p && attacker.hasSubtype subtype
      | _ => false

/-- A permanent of `subtype` entered under `p`'s control on `turn`. -/
def subtypeEntered (events : Array GameEvent) (turn : Nat) (p : PlayerId)
    (subtype : String) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .moved object _ .battlefield _ _ =>
        object.controller == some p && object.hasSubtype subtype
      | .created q object => q == p && object.hasSubtype subtype
      | _ => false

/-- `p` activated a loyalty ability on `turn`. -/
def activatedLoyalty (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .activated q _ true _ => q == p
      | _ => false

/-- `p` was dealt noncombat damage on `turn`. -/
def dealtNoncombat (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .damagedPlayer _ q _ false => q == p
      | .life q _ false true false => q == p
      | _ => false

/-- Mana recorded for `spell` when it was cast, if the log has that cast. -/
def manaSpentOn (events : Array GameEvent) (spell : ObjectId) : Nat :=
  events.foldl (fun n e =>
    match e.change with
    | .cast _ s _ _ spent _ _ _ => if s.id == spell then max n spent else n
    | _ => n) 0

/-- Same event, naming the object id it has after the zone change (CR 400.7). -/
def withObjectId (e : GameEvent) (id : ObjectId) : GameEvent :=
  match e.change with
  | .moved object fromZone toZone sacrificed discarded =>
    { e with change := .moved { object with id := id } fromZone toZone sacrificed discarded }
  | .created player object =>
    { e with change := .created player { object with id := id } }
  | _ => e

/-- Creature spells `p` cast on `turn`. -/
def creatureSpells (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .cast q spell _ _ _ _ _ _ => if q == p && spell.creature then n + 1 else n
      | _ => n) 0

/-- Noncreature spells `p` cast on `turn`. -/
def noncreatureSpells (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .cast q spell _ _ _ _ _ _ => if q == p && !spell.creature then n + 1 else n
      | _ => n) 0

/-- Creatures `p` attacked with on `turn`. -/
def attacks (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .attacked q _ _ => if q == p then n + 1 else n
      | _ => n) 0

/-- Cards that moved from `p`'s library to `p`'s graveyard on `turn`. -/
def milled (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .moved _ (.library owner) (.graveyard q) _ _ =>
        if owner == p && q == p then n + 1 else n
      | _ => n) 0

/-- `p` has already drawn the first card of their draw step on `turn`. -/
def drewFirstOfDrawStep (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .drew q _ _ true => q == p
      | _ => false

/-- Equip abilities `p` completed on `turn`. -/
def equipActivations (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .activated q _ _ true => if q == p then n + 1 else n
      | _ => n) 0

/-- Mana values of spells `p` cast on `turn`, oldest first. Copies are absent. -/
def castManaValues (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Array Nat :=
  events.foldl (fun acc e =>
    if e.turn != turn then acc
    else
      match e.change with
      | .cast q _ _ mv _ _ _ _ => if q == p then acc.push mv else acc
      | _ => acc) #[]

/-- Cards `p` discarded on `turn`. A discard is a card moving from that
player's hand to their graveyard. -/
def discards (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .moved _ (.hand q) (.graveyard r) _ true => if q == p && q == r then n + 1 else n
      | _ => n) 0

/-- Life `p` lost on `turn`, including life lost to damage. -/
def lifeLost (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .life q amount false _ _ => if q == p then n + amount else n
      | _ => n) 0

/-- Counted resolutions for `p` on `turn`. -/
def resolutions (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .resolved q _ => if q == p then n + 1 else n
      | _ => n) 0

/-- Lands `p` played on `turn`. -/
def landsPlayed (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .playedLand q _ => if q == p then n + 1 else n
      | _ => n) 0

/-- Graveyard ids of creatures that moved from the battlefield to a graveyard
on `turn`. The id is the one the card has after it arrives (CR 400.7). -/
def creaturesToGraveyard (events : Array GameEvent) (turn : Nat) : Array ObjectId :=
  events.foldl (fun acc e =>
    if e.turn != turn then acc
    else
      match e.change with
      | .moved object .battlefield (.graveyard _) _ _ =>
        if object.creature then acc.push object.id else acc
      | _ => acc) #[]

/-- Graveyard id of the most recent attacking creature that died. -/
def lastDiedAttacker (events : Array GameEvent) : Option ObjectId :=
  events.foldl (fun acc e =>
    match e.change with
    | .moved object .battlefield (.graveyard _) _ _ =>
      if object.creature && object.attacking then some object.id else acc
    | _ => acc) none

/-- Id of the permanent that most recently became tapped. -/
def lastBecameTapped (events : Array GameEvent) : Option ObjectId :=
  events.foldl (fun acc e =>
    match e.change with
    | .tapped object true _ => some object.id
    | _ => acc) none

/-- Player most recently dealt combat damage. -/
def lastCombatDamagePlayer (events : Array GameEvent) : Option PlayerId :=
  events.foldl (fun acc e =>
    match e.change with
    | .damagedPlayer _ p _ true => some p
    | _ => acc) none

/-- Someone chose to have The Sensational She-Hulk deal damage on `turn`. -/
def sheHulkDealtDamageThisTurn (events : Array GameEvent) (turn : Nat) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .sheHulkDealtDamage _ => true
      | _ => false

/-- `id` entered the battlefield on `turn`. -/
def objectEntered (events : Array GameEvent) (turn : Nat) (id : ObjectId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .moved object _ .battlefield _ _ => object.id == id
      | .created _ object => object.id == id
      | _ => false

/-- The cast of `spell` was from a graveyard. -/
def castFromGraveyard (events : Array GameEvent) (spell : ObjectId) : Bool :=
  events.any fun e =>
    match e.change with
    | .cast _ s _ _ _ true _ _ => s.id == spell
    | _ => false

/-- A gift was promised as `spell` was cast. -/
def giftPromised (events : Array GameEvent) (spell : ObjectId) : Bool :=
  events.any fun e =>
    match e.change with
    | .cast _ s _ _ _ _ _ true => s.id == spell
    | _ => false

/-- `spell` was cast using teamwork. -/
def teamwork (events : Array GameEvent) (spell : ObjectId) : Bool :=
  events.any fun e =>
    match e.change with
    | .cast _ s _ _ _ _ true _ => s.id == spell
    | _ => false

end GameEvent

end Mtg.Engine
