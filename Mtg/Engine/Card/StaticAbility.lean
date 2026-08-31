import Mtg.Engine.Mana
import Mtg.Engine.TypeLine
import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.Text

/-!
# Static abilities (CR 604)

The static abilities the engine understands, their shared `StaticShape`
spec table, and Oracle-text rendering.
-/

namespace Mtg.Engine

/-- A static ability the engine currently understands (CR 604). -/
inductive StaticAbility where
  /-- Other creatures you control that have any of these subtypes have trample
  (e.g. Orcish Siegemaster). -/
  | otherCreaturesHaveTrample (subtypes : Array String)
  /-- Other creatures you control that have any of these subtypes get +P/+T
  (e.g. Elvish Archdruid). -/
  | otherCreaturesGet (subtypes : Array String) (power toughness : Int)
  /-- Enchanted creature gets +P/+T (e.g. Gift of Strands). -/
  | enchantedCreatureGets (power toughness : Int)
  /-- Equipped creature gets +P/+T (e.g. Ragged Short Spear). -/
  | equippedCreatureGets (power toughness : Int)
  /-- This creature's power and toughness are each equal to the number of lands
  you control. A characteristic-defining ability that functions in all zones
  (CR 208.2a / 604.3), e.g. Mirkwood Pathmaker and animated Beorn's Hospitality. -/
  | powerToughnessEqualLandsYouControl
  /-- This creature can't block unless its controller controls a permanent with
  any of these subtypes (e.g. Olog-hai Crusher). An empty list means it can't
  block at all. The restriction is checked when declaring blockers (CR 509.1b). -/
  | cantBlockUnlessYouControl (subtypes : Array String)
  /-- This creature can't be blocked except by `n` or more creatures
  (e.g. Troll of Khazad-dûm with 3). Menace is the keyword for `n = 2`. -/
  | cantBeBlockedExceptBy (n : Nat)
  /-- Enchanted creature is only this subtype and can't attack or block
  (e.g. Fog on the Barrow-Downs). -/
  | enchantedIsOnlySubtypeCantAttackOrBlock (subtype : String)
  /-- This creature's power is equal to the number of cards in your hand
  (e.g. Minas Tirith Garrison). -/
  | powerEqualCardsInHand
  /-- Equipped creature has these keywords. -/
  | equippedCreatureHasKeywords (k : Keywords)
  /-- Enchanted creature gets +P/+T and has these keywords. -/
  | enchantedCreatureGetsAndHas (power toughness : Int) (k : Keywords)
  /-- This creature can't be blocked by tokens. -/
  | cantBeBlockedByTokens
  /-- This creature's power is equal to the number of creatures you control. -/
  | powerEqualCreaturesYouControl
  /-- Armies you control have trample. -/
  | armiesYouControlHaveTrample
  /-- Creatures you control (including this) get +P/+T. -/
  | creaturesYouControlGet (power toughness : Int)
  /-- This has haste as long as you control another permanent of this subtype. -/
  | hasteIfYouControlOtherSubtype (subtype : String)
  /-- This can't attack unless you control `n` or more other permanents of
  this subtype. -/
  | cantAttackUnlessYouControlNOther (n : Nat) (subtype : String)
  /-- Legendary creatures you control get +P/+T and have ward `{w}`. -/
  | legendaryCreaturesGetAndWard (power toughness : Int) (ward : Nat)
  /-- Nonlegendary creatures you control get +P/+T. -/
  | nonlegendaryCreaturesGet (power toughness : Int)
  /-- Equipped creature gets +P/+T and has these keywords. -/
  | equippedCreatureGetsAndHas (power toughness : Int) (k : Keywords)
  /-- Equipped creature gets +P/+T and has ward `{w}`. -/
  | equippedCreatureGetsAndWard (power toughness : Int) (ward : Nat)
  /-- Each creature you control with a +1/+1 counter has menace. -/
  | creaturesYouControlWithPlusOneHaveMenace
  /-- This has lifelink as long as you control another of this subtype. -/
  | lifelinkIfYouControlOtherSubtype (subtype : String)
  /-- Threshold — this gets +P/+T if there are seven or more cards in your
  graveyard. -/
  | thresholdGets (power toughness : Int)
  /-- This can't be blocked by creatures with power `n` or less. -/
  | cantBeBlockedByPowerAtMost (n : Int)
  /-- During your turn, equipped creatures you control have these keywords. -/
  | equippedCreaturesHaveKeywordsDuringYourTurn (k : Keywords)
  /-- As long as you have an enduring story, this gets +P/+T and has these
  keywords. -/
  | getsAndHasIfEnduringStory (power toughness : Int) (k : Keywords)
  /-- As long as you have an enduring story, creatures you control get +P/+T. -/
  | creaturesYouControlGetIfEnduringStory (power toughness : Int)
  /-- This doesn't untap during your untap step unless you have an enduring
  story. -/
  | doesntUntapUnlessEnduringStory
  /-- As long as you have an enduring story, artifacts and creatures you
  control have ward `{w}`. -/
  | artifactsAndCreaturesHaveWardIfEnduringStory (ward : Nat)
  /-- As long as you have an enduring story, creatures can't attack you unless
  their controller pays `{n}` for each. -/
  | creaturesCantAttackYouUnlessPayIfEnduringStory (n : Nat)
  /-- Other permanents of these subtypes have `{T}: Add one of these types`. -/
  | otherSubtypeHaveTapAddOneOf (subtypes : Array String) (mana : Array ManaType)
  /-- This can't be blocked by creatures with power `n` or greater. -/
  | cantBeBlockedByPowerAtLeast (n : Int)
  /-- Equipped creature has these keywords and can't be blocked. -/
  | equippedCreatureHasKeywordsAndCantBeBlocked (k : Keywords)
  /-- Equip abilities that target this cost `{n}` less. -/
  | equipAbilitiesTargetingThisCostLess (n : Nat)
  /-- As long as you have an enduring story, the first equip each turn is `{0}`. -/
  | firstEquipFreeIfEnduringStory
  /-- Creatures you control of the chosen type get +P/+T. -/
  | chosenTypeCreaturesGet (power toughness : Int)
  /-- Instant and sorcery spells cost {X} less, X = equipped creature's power. -/
  | instantSorceryCostReductionEqualEquippedPower
  /-- Other permanents of this subtype get +P/+0 for each artifact token. -/
  | otherSubtypeGetPowerPerArtifactToken (subtype : String)
  /-- As long as you have an enduring story, Dwarf triggers go twice. -/
  | extraTriggerIfEnduringStorySubtype (subtype : String)
  /-- If a triggered ability of another matching permanent you control
  triggers, it triggers an additional time (e.g. Chief of the Wilds). -/
  | extraTriggerAnotherYouControl (subtypes : Array String) (includeBattles : Bool)
  /-- Enchanted creature loses all abilities and doesn't untap. -/
  | enchantedLosesAbilitiesDoesntUntap
  /-- During your turn, equipped creature has hexproof and can't be blocked. -/
  | equippedHexproofUnblockableDuringYourTurn
  /-- If a triggered ability of equipped creature triggers, it triggers again. -/
  | equippedTriggersAgain
  /-- Equipped creature has first strike and gets +1/+0 per instant/sorcery
  in your graveyard. -/
  | equippedFirstStrikePlusPerInstantSorcery
  /-- This gets +P/+0 for each graveyard with seven or more cards. -/
  | powerPerFatGraveyard (power : Int)
  /-- If an opposing creature would die, exile it and create a Wolf. -/
  | exileOppDeathCreateWolf
  /-- This has all activated abilities of cards of this subtype in your
  graveyard. -/
  | copyActivatedFromGySubtype (subtype : String)
  /-- Equipped creature gets +P/+T and has trample and a combat Treasure
  trigger. -/
  | equippedGetsTrampleAndCombatTreasures (power toughness : Int)
  /-- Ward — discard an enchantment, instant, or sorcery card. -/
  | wardDiscardEnchantmentInstantOrSorcery
  /-- Ward — sacrifice a legendary artifact or legendary creature. -/
  | wardSacrificeLegendary
  /-- Creatures you control of this subtype get +P/+T (includes the source). -/
  | creaturesYouControlOfSubtypeGet (subtype : String) (power toughness : Int)
  /-- You and other permanents of this subtype have hexproof while this has
  a shield counter. -/
  | youAndOtherSubtypeHaveHexproofIfShield (subtype : String)
  /-- Opponents can't cast spells during your turn. -/
  | opponentsCantCastOnYourTurn
  /-- Spells of this subtype you cast cost `{n}` less. -/
  | subtypeSpellsCostLess (subtype : String) (n : Nat)
  /-- This creature can't be blocked if its power is `n` or less. -/
  | cantBeBlockedIfPowerAtMost (n : Int)
  /-- Prevent all damage that would be dealt to this permanent. -/
  | preventAllDamageToThis
  /-- You have no maximum hand size. -/
  | noMaximumHandSize
  /-- Your maximum hand size is `n`. -/
  | maximumHandSize (n : Nat)
  /-- This creature's power is equal to the number of permanents you control
  of this subtype (e.g. Namor and Merfolk). -/
  | powerEqualSubtypeYouControl (subtype : String)
  /-- This creature's power is equal to the number of legendary creatures
  you control (e.g. Super-Adaptoid). -/
  | powerEqualLegendaryCreaturesYouControl
  /-- Spells of this card type you cast cost `{n}` less (e.g. artifact spells). -/
  | typeSpellsCostLess (ty : CardType) (n : Nat)
  /-- Improvise (CR 702.126). -/
  | improvise
  /-- Noncreature spells you cast have improvise. -/
  | noncreatureSpellsHaveImprovise
  /-- Extort (CR 702.83). -/
  | extort
  /-- Attacking creature tokens you control have these keywords. -/
  | attackingTokensHave (k : Keywords)
  /-- Each creature you put a +1/+1 counter on this turn has hexproof. -/
  | hexproofIfPlusOneThisTurn
  /-- You may play lands from your graveyard. -/
  | mayPlayLandsFromGraveyard
  /-- As long as an opponent has cast a spell this turn, you may cast spells
  as though they had flash. -/
  | flashIfOpponentCastThisTurn
  /-- Ward — discard a card or pay `{n}`. -/
  | wardDiscardOrPay (n : Nat)
  /-- Ward — get `n` poison counters. -/
  | wardPoisonCounters (n : Nat)
  /-- This creature attacks each combat if able. -/
  | attacksEachCombatIfAble
  /-- Instant and sorcery spells you cast with mana value 4 or greater cost
  {X} less, where X is this creature's power. -/
  | instantSorceryCostLessEqualPower
  /-- Each power-up ability of permanents you control can be activated an
  additional time. -/
  | extraPowerUpActivation
  /-- Power-up abilities of other creatures you control cost `{n}` less. -/
  | otherPowerUpCostsLess (n : Nat)
  /-- You may activate abilities of creatures you control as though they had
  haste. -/
  | activateCreaturesAsThoughHaste
  /-- If you would put one or more counters on a permanent you control, put
  that many plus one of each of those kinds instead. -/
  | extraCounterOnPermanents
  /-- If this is in your opening hand, you may begin the game with it on
  the battlefield. -/
  | mayBeginOnBattlefield
  /-- Enchanted creature has ward `{w}`. -/
  | enchantedCreatureHasWard (w : Nat)
  /-- Equipped creature gets +P/+T and has these keywords and ward `{w}`. -/
  | equippedCreatureGetsHasAndWard (power toughness : Int) (k : Keywords) (w : Nat)
  /-- Creatures you control with +1/+1 counters on them have these keywords. -/
  | creaturesWithPlusOneHave (k : Keywords)
  /-- Creatures your opponents control get +P/+T. -/
  | opponentsCreaturesGet (power toughness : Int)
  /-- This gets +P/+0 for each other artifact you control. -/
  | getsPowerPerOtherArtifact (power : Int)
  /-- This gets +P/+0 for each Equipment attached to it. -/
  | getsPowerPerAttachedEquipment (power : Int)
  /-- As long as there are at least `min` creature cards in your graveyard,
  this gets +P/+T. -/
  | getsIfGyCreatureCards (min : Nat) (power toughness : Int)
  /-- This has indestructible as long as you control an artifact creature
  or a Plan. -/
  | indestructibleIfArtifactCreatureOrPlan
  /-- This has flying as long as you put a +1/+1 counter on it this turn. -/
  | flyingIfPlusOneThisTurn
  /-- Creatures with flying can't attack you or block creatures you control. -/
  | flyingCantAttackYouOrBlockYours
  /-- If a creature you control would connive, you draw first, then it connives. -/
  | extraDrawOnConnive
  /-- If a source you control would deal noncombat damage, it deals that
  much plus this creature's power instead. -/
  | noncombatDamagePlusSourcePower
  /-- Double all damage equipped creature would deal. -/
  | equippedDealsDoubleDamage
  /-- If damage would be dealt to this, it is dealt but prior damage is healed. -/
  | healOtherDamageWhenDealt
  /-- This enters with X +1/+1 counters. -/
  | entersWithXPlusOne
  /-- Enchanted creature gets +P/+T and has these keywords, and may gain
  additional types. -/
  | enchantedCreatureGetsHasAndTypes (power toughness : Int) (k : Keywords)
    (types : Array String)
  /-- Enchanted creature loses all abilities and can't become untapped. -/
  | enchantedLosesAbilitiesCantUntap
  /-- Enchanted creature gets +P/+T and has these keywords and ward `{w}`. -/
  | enchantedCreatureGetsHasAndWard (power toughness : Int) (k : Keywords)
    (w : Nat)
  /-- As long as there are at least `min` creature cards in your graveyard,
  this gets +P/+T and is all creature types. -/
  | getsAndAllTypesIfGyCreatureCards (min : Nat) (power toughness : Int)
  /-- Sneak `cost` (cast by returning an unblocked attacker). -/
  | sneak (cost : ManaCost)
  /-- Boast — exile black cards from your graveyard and copy them. -/
  | boast
deriving Repr, Inhabited, BEq

namespace StaticAbility

/-- English plural used in Oracle-style reminders (`Orc` → `Orcs`), including
the irregular plurals the catalog prints. -/
def pluralSubtype (s : String) : String :=
  match s with
  | "Army" => "Armies"
  | "Elf" => "Elves"
  | "Wolf" => "Wolves"
  | "Dwarf" => "Dwarves"
  | "Hero" => "Heroes"
  | "Merfolk" => "Merfolk"
  | s => if s.endsWith "s" then s else s ++ "s"

#guard pluralSubtype "Orc" == "Orcs"
#guard pluralSubtype "Wolf" == "Wolves"
#guard pluralSubtype "Army" == "Armies"
#guard pluralSubtype "Hero" == "Heroes"
#guard pluralSubtype "Merfolk" == "Merfolk"

/-- Oracle-style “Enchanted/Equipped creature gets +P/+T.” -/
def hostGetsPhrase (host : String) (p t : Int) : String :=
  s!"{host} gets {signedStat p}/{signedStat t}."

/-- Join subtype names for Oracle-style lord reminders (`Orc` and `Goblin`). -/
def joinedSubtypes (subtypes : Array String) (each : String → String := fun s => s) : String :=
  String.intercalate " and " (subtypes.toList.map each)

/-- How a static ability applies (CR 604 / 613). Grouped so Game accessors and
`toNotation` match a handful of shapes instead of every constructor. Enchanted
and equipped host pumps share `hostGets`. -/
inductive StaticShape where
  /-- Other matching creatures you control have trample. -/
  | lordTrample (subtypes : Array String)
  /-- Other matching creatures you control get +P/+T. -/
  | lordPump (subtypes : Array String) (power toughness : Int)
  /-- The enchanted or equipped host gets +P/+T. -/
  | hostGets (host : String) (power toughness : Int)
  /-- Characteristic-defining P/T equal to lands you control. -/
  | landsYouControlPT
  /-- This creature can't block unless you control a listed subtype. -/
  | cantBlockUnless (subtypes : Array String)
  /-- This creature can't be blocked except by `n` or more creatures. -/
  | cantBeBlockedExcept (n : Nat)
  /-- Enchanted creature is only this subtype and can't attack or block. -/
  | enchantedOnlySubtypeCantAttackOrBlock (subtype : String)
  /-- Characteristic-defining power equal to cards in your hand. -/
  | cardsInHandPower
  /-- Equipped or enchanted host has these keywords, and optionally +P/+T. -/
  | hostKeywords (host : String) (k : Keywords) (power toughness : Int)
  /-- This creature can't be blocked by tokens. -/
  | cantBeBlockedByTokens
  /-- Characteristic-defining power equal to creatures you control. -/
  | creaturesYouControlPower
  /-- Creatures you control of this subtype have trample. -/
  | youControlSubtypeTrample (subtype : String)
  /-- Creatures you control get +P/+T (includes the source). -/
  | teamPump (power toughness : Int) (legendaryOnly nonlegendaryOnly : Bool)
  /-- This has haste while you control another of this subtype. -/
  | hasteIfOtherSubtype (subtype : String)
  /-- This can't attack unless you control `n` other permanents of this subtype. -/
  | cantAttackUnlessNOther (n : Nat) (subtype : String)
  /-- Legendary creatures you control get +P/+T and have ward `{w}`. -/
  | legendaryTeamPumpWard (power toughness : Int) (ward : Nat)
  /-- Equipped/enchanted host gets +P/+T and has ward `{w}`. -/
  | hostGetsAndWard (host : String) (power toughness : Int) (ward : Nat)
  /-- Creatures you control with a +1/+1 counter have menace. -/
  | creaturesWithPlusOneHaveMenace
  /-- This has lifelink while you control another of this subtype. -/
  | lifelinkIfOtherSubtype (subtype : String)
  /-- Threshold +P/+T. -/
  | thresholdGets (power toughness : Int)
  /-- Can't be blocked by creatures with power `n` or less. -/
  | cantBeBlockedByPowerAtMost (n : Int)
  /-- During your turn, equipped creatures you control have these keywords. -/
  | equippedTeamKeywordsDuringYourTurn (k : Keywords)
  /-- Enduring-story self pump and keywords. -/
  | selfIfEnduringStory (power toughness : Int) (k : Keywords)
  /-- Enduring-story team pump. -/
  | teamIfEnduringStory (power toughness : Int)
  /-- Doesn't untap unless enduring story. -/
  | doesntUntapUnlessEnduringStory
  /-- Artifacts and creatures you control have ward if enduring story. -/
  | teamWardIfEnduringStory (ward : Nat)
  /-- Attack tax if enduring story. -/
  | attackTaxIfEnduringStory (n : Nat)
  /-- Other matching permanents have a tap-add-one-of mana ability. -/
  | otherSubtypeTapAddOneOf (subtypes : Array String) (mana : Array ManaType)
  /-- Can't be blocked by creatures with power `n` or greater. -/
  | cantBeBlockedByPowerAtLeast (n : Int)
  /-- Equipped creature has keywords and can't be blocked. -/
  | equippedKeywordsAndUnblockable (k : Keywords)
  /-- Equip abilities targeting this cost less. -/
  | equipTargetingThisCostLess (n : Nat)
  /-- First equip each turn is free if enduring story. -/
  | firstEquipFreeIfEnduringStory
  /-- Chosen-type team pump. -/
  | chosenTypePump (power toughness : Int)
  /-- Instant/sorcery cost reduction equal to equipped power. -/
  | instantSorceryCostReductionEqualEquippedPower
  /-- Other matching creatures get +P/+0 per artifact token. -/
  | otherSubtypePowerPerArtifactToken (subtype : String)
  | extraTriggerIfEnduringStorySubtype (subtype : String)
  | extraTriggerAnotherYouControl (subtypes : Array String) (includeBattles : Bool)
  | enchantedLosesAbilitiesDoesntUntap
  | equippedHexproofUnblockableDuringYourTurn
  | equippedTriggersAgain
  | equippedFirstStrikePlusPerInstantSorcery
  | powerPerFatGraveyard (power : Int)
  | exileOppDeathCreateWolf
  | copyActivatedFromGySubtype (subtype : String)
  | equippedGetsTrampleAndCombatTreasures (power toughness : Int)
  | wardDiscardEnchantmentInstantOrSorcery
  | wardSacrificeLegendary
  | teamPumpSubtype (subtype : String) (power toughness : Int)
  | youAndOtherSubtypeHexproofIfShield (subtype : String)
  | opponentsCantCastOnYourTurn
  | subtypeSpellsCostLess (subtype : String) (n : Nat)
  | cantBeBlockedIfPowerAtMost (n : Int)
  | preventAllDamageToThis
  | noMaximumHandSize
  | maximumHandSize (n : Nat)
  | powerEqualSubtype (subtype : String)
  | powerEqualLegendaryCreatures
  | typeSpellsCostLess (ty : CardType) (n : Nat)
  | improvise
  | noncreatureSpellsHaveImprovise
  | extort
  | attackingTokensHave (k : Keywords)
  | hexproofIfPlusOneThisTurn
  | mayPlayLandsFromGraveyard
  | flashIfOpponentCastThisTurn
  | wardDiscardOrPay (n : Nat)
  | wardPoisonCounters (n : Nat)
  | attacksEachCombatIfAble
  | instantSorceryCostLessEqualPower
  | extraPowerUpActivation
  | otherPowerUpCostsLess (n : Nat)
  | activateCreaturesAsThoughHaste
  | extraCounterOnPermanents
  | mayBeginOnBattlefield
  | enchantedHasWard (w : Nat)
  | equippedGetsHasAndWard (power toughness : Int) (k : Keywords) (w : Nat)
  | creaturesWithPlusOneHave (k : Keywords)
  | opponentsCreaturesGet (power toughness : Int)
  | getsPowerPerOtherArtifact (power : Int)
  | getsPowerPerAttachedEquipment (power : Int)
  | getsIfGyCreatureCards (min : Nat) (power toughness : Int)
  | indestructibleIfArtifactCreatureOrPlan
  | flyingIfPlusOneThisTurn
  | flyingCantAttackYouOrBlockYours
  | extraDrawOnConnive
  | noncombatDamagePlusSourcePower
  | equippedDealsDoubleDamage
  | healOtherDamageWhenDealt
  | entersWithXPlusOne
  | enchantedGetsHasAndTypes (power toughness : Int) (k : Keywords)
    (types : Array String)
  | enchantedLosesAbilitiesCantUntap
  | enchantedGetsHasAndWard (power toughness : Int) (k : Keywords) (w : Nat)
  | getsAndAllTypesIfGyCreatureCards (min : Nat) (power toughness : Int)
  | sneak (cost : ManaCost)
  | boast
deriving Repr, Inhabited, BEq

/-- Projections Game reads from a static shape. Exhaustive so a new shape is a
compile error here rather than silently matching `none` / `(0, 0)` / `false`. -/
structure StaticMeta where
  lordPump : Option (Array String × Int × Int) := none
  trampleSubtypes : Option (Array String) := none
  hostBonus : Int × Int := (0, 0)
  landsYouControlPT : Bool := false
  cantBlockUnless : Option (Array String) := none
  cantBeBlockedExcept : Option Nat := none
  enchantedOnlySubtype : Option String := none
  cardsInHandPower : Bool := false
  hostKeywords : Keywords := Keywords.none
  cantBeBlockedByTokens : Bool := false
  creaturesYouControlPower : Bool := false
  /-- Lord pump includes the source (not only other creatures). -/
  lordIncludesSelf : Bool := false
  /-- Lord pump applies only to legendary creatures. -/
  lordLegendaryOnly : Bool := false
  /-- Lord pump applies only to nonlegendary creatures. -/
  lordNonlegendaryOnly : Bool := false
  /-- Ward cost this ability grants matching creatures. -/
  grantedWard : Option Nat := none
  /-- This has haste while you control another of this subtype. -/
  hasteIfOtherSubtype : Option String := none
  /-- Can't attack unless you control this many other permanents of the subtype. -/
  cantAttackUnlessNOther : Option (Nat × String) := none
  /-- Creatures you control with a +1/+1 counter have menace. -/
  creaturesWithPlusOneHaveMenace : Bool := false
  /-- This has lifelink while you control another of this subtype. -/
  lifelinkIfOtherSubtype : Option String := none
  /-- Threshold +P/+T if seven or more cards in graveyard. -/
  thresholdGets : Option (Int × Int) := none
  /-- Can't be blocked by creatures with power at most this. -/
  cantBeBlockedByPowerAtMost : Option Int := none
  /-- This creature can't be blocked if its own power is at most this. -/
  cantBeBlockedIfPowerAtMost : Option Int := none
  /-- During your turn, equipped creatures you control have these keywords. -/
  equippedTeamKeywordsDuringYourTurn : Keywords := Keywords.none
  /-- Enduring-story self pump. -/
  selfIfEnduringStory : Option (Int × Int × Keywords) := none
  /-- Enduring-story team pump. -/
  teamIfEnduringStory : Option (Int × Int) := none
  /-- Doesn't untap unless enduring story. -/
  doesntUntapUnlessEnduringStory : Bool := false
  /-- Team ward if enduring story. -/
  teamWardIfEnduringStory : Option Nat := none
  /-- Attack tax `{n}` if enduring story. -/
  attackTaxIfEnduringStory : Option Nat := none
  /-- Can't be blocked by creatures with power at least this. -/
  cantBeBlockedByPowerAtLeast : Option Int := none
  /-- Equipped creature also can't be blocked. -/
  equippedCantBeBlocked : Bool := false
  /-- Equip abilities targeting this cost this much less. -/
  equipTargetingThisCostLess : Option Nat := none
  /-- First equip is free if enduring story. -/
  firstEquipFreeIfEnduringStory : Bool := false
  /-- You have no maximum hand size. -/
  noMaximumHandSize : Bool := false
  /-- Your maximum hand size, if this ability sets one. -/
  maximumHandSize : Option Nat := none
  /-- Power equal to permanents you control of this subtype. -/
  powerEqualSubtype : Option String := none
  /-- Power equal to legendary creatures you control. -/
  powerEqualLegendaryCreatures : Bool := false
deriving Repr, Inhabited, BEq

/-- Classification of a static shape for Game accessors. -/
def StaticShape.spec : StaticShape → StaticMeta
  | .lordTrample subtypes => { trampleSubtypes := some subtypes }
  | .lordPump subtypes p t => { lordPump := some (subtypes, p, t) }
  | .hostGets _ p t => { hostBonus := (p, t) }
  | .landsYouControlPT => { landsYouControlPT := true }
  | .cantBlockUnless subtypes => { cantBlockUnless := some subtypes }
  | .cantBeBlockedExcept n => { cantBeBlockedExcept := some n }
  | .enchantedOnlySubtypeCantAttackOrBlock subtype =>
    { enchantedOnlySubtype := some subtype }
  | .cardsInHandPower => { cardsInHandPower := true }
  | .hostKeywords _ k p t => { hostKeywords := k, hostBonus := (p, t) }
  | .cantBeBlockedByTokens => { cantBeBlockedByTokens := true }
  | .creaturesYouControlPower => { creaturesYouControlPower := true }
  | .youControlSubtypeTrample subtype => { trampleSubtypes := some #[subtype] }
  | .teamPump p t legendaryOnly nonlegendaryOnly =>
    { lordPump := some (#[], p, t), lordIncludesSelf := true,
      lordLegendaryOnly := legendaryOnly, lordNonlegendaryOnly := nonlegendaryOnly }
  | .hasteIfOtherSubtype subtype => { hasteIfOtherSubtype := some subtype }
  | .cantAttackUnlessNOther n subtype => { cantAttackUnlessNOther := some (n, subtype) }
  | .legendaryTeamPumpWard p t w =>
    { lordPump := some (#[], p, t), lordIncludesSelf := true, lordLegendaryOnly := true,
      grantedWard := some w }
  | .hostGetsAndWard _ p t w =>
    { hostBonus := (p, t), grantedWard := some w }
  | .creaturesWithPlusOneHaveMenace =>
    { creaturesWithPlusOneHaveMenace := true }
  | .lifelinkIfOtherSubtype subtype =>
    { lifelinkIfOtherSubtype := some subtype }
  | .thresholdGets p t =>
    { thresholdGets := some (p, t) }
  | .cantBeBlockedByPowerAtMost n =>
    { cantBeBlockedByPowerAtMost := some n }
  | .equippedTeamKeywordsDuringYourTurn k =>
    { equippedTeamKeywordsDuringYourTurn := k }
  | .selfIfEnduringStory p t k =>
    { selfIfEnduringStory := some (p, t, k) }
  | .teamIfEnduringStory p t =>
    { teamIfEnduringStory := some (p, t) }
  | .doesntUntapUnlessEnduringStory =>
    { doesntUntapUnlessEnduringStory := true }
  | .teamWardIfEnduringStory w =>
    { teamWardIfEnduringStory := some w }
  | .attackTaxIfEnduringStory n =>
    { attackTaxIfEnduringStory := some n }
  | .otherSubtypeTapAddOneOf _ _ => {}
  | .cantBeBlockedByPowerAtLeast n =>
    { cantBeBlockedByPowerAtLeast := some n }
  | .equippedKeywordsAndUnblockable k =>
    { hostKeywords := k, equippedCantBeBlocked := true }
  | .equipTargetingThisCostLess n =>
    { equipTargetingThisCostLess := some n }
  | .firstEquipFreeIfEnduringStory =>
    { firstEquipFreeIfEnduringStory := true }
  | .chosenTypePump p t =>
    { lordPump := some (#[], p, t), lordIncludesSelf := true }
  | .instantSorceryCostReductionEqualEquippedPower => {}
  | .otherSubtypePowerPerArtifactToken _ => {}
  | .extraTriggerIfEnduringStorySubtype _ => {}
  | .extraTriggerAnotherYouControl _ _ => {}
  | .enchantedLosesAbilitiesDoesntUntap => {}
  | .equippedHexproofUnblockableDuringYourTurn => {}
  | .equippedTriggersAgain => {}
  | .equippedFirstStrikePlusPerInstantSorcery =>
    { hostKeywords := Keyword.firstStrike }
  | .powerPerFatGraveyard _ => {}
  | .exileOppDeathCreateWolf => {}
  | .copyActivatedFromGySubtype _ => {}
  | .equippedGetsTrampleAndCombatTreasures p t =>
    { hostBonus := (p, t) }
  | .wardDiscardEnchantmentInstantOrSorcery => {}
  | .wardSacrificeLegendary => {}
  | .teamPumpSubtype subtype p t =>
    { lordPump := some (#[subtype], p, t), lordIncludesSelf := true }
  | .youAndOtherSubtypeHexproofIfShield _ => {}
  | .opponentsCantCastOnYourTurn => {}
  | .subtypeSpellsCostLess _ _ => {}
  | .cantBeBlockedIfPowerAtMost n =>
    { cantBeBlockedIfPowerAtMost := some n }
  | .preventAllDamageToThis => {}
  | .noMaximumHandSize => { noMaximumHandSize := true }
  | .maximumHandSize n => { maximumHandSize := some n }
  | .powerEqualSubtype subtype => { powerEqualSubtype := some subtype }
  | .powerEqualLegendaryCreatures => { powerEqualLegendaryCreatures := true }
  | .typeSpellsCostLess _ _ => {}
  | .improvise => {}
  | .noncreatureSpellsHaveImprovise => {}
  | .extort => {}
  | .attackingTokensHave _ => {}
  | .hexproofIfPlusOneThisTurn => {}
  | .mayPlayLandsFromGraveyard => {}
  | .flashIfOpponentCastThisTurn => {}
  | .wardDiscardOrPay _ => {}
  | .wardPoisonCounters _ => {}
  | .attacksEachCombatIfAble => {}
  | .instantSorceryCostLessEqualPower => {}
  | .extraPowerUpActivation => {}
  | .otherPowerUpCostsLess _ => {}
  | .activateCreaturesAsThoughHaste => {}
  | .extraCounterOnPermanents => {}
  | .mayBeginOnBattlefield => {}
  | .enchantedHasWard w => { grantedWard := some w }
  | .equippedGetsHasAndWard p t k w =>
    { hostBonus := (p, t), hostKeywords := k, grantedWard := some w }
  | .creaturesWithPlusOneHave _ => {}
  | .opponentsCreaturesGet _ _ => {}
  | .getsPowerPerOtherArtifact _ => {}
  | .getsPowerPerAttachedEquipment _ => {}
  | .getsIfGyCreatureCards _ _ _ => {}
  | .indestructibleIfArtifactCreatureOrPlan => {}
  | .flyingIfPlusOneThisTurn => {}
  | .flyingCantAttackYouOrBlockYours => {}
  | .extraDrawOnConnive => {}
  | .noncombatDamagePlusSourcePower => {}
  | .equippedDealsDoubleDamage => {}
  | .healOtherDamageWhenDealt => {}
  | .entersWithXPlusOne => {}
  | .enchantedGetsHasAndTypes p t k _ =>
    { hostBonus := (p, t), hostKeywords := k }
  | .enchantedLosesAbilitiesCantUntap => {}
  | .enchantedGetsHasAndWard p t k w =>
    { hostBonus := (p, t), hostKeywords := k, grantedWard := some w }
  | .getsAndAllTypesIfGyCreatureCards _ _ _ => {}
  | .sneak _ => {}
  | .boast => {}

/-- Classification of this static ability. Exhaustive so a new constructor is a
compile error here rather than silently matching `false` / `(0, 0)` in `Game`. -/
def shape : StaticAbility → StaticShape
  | .otherCreaturesHaveTrample subtypes => .lordTrample subtypes
  | .otherCreaturesGet subtypes p t => .lordPump subtypes p t
  | .enchantedCreatureGets p t => .hostGets "Enchanted creature" p t
  | .equippedCreatureGets p t => .hostGets "Equipped creature" p t
  | .powerToughnessEqualLandsYouControl => .landsYouControlPT
  | .cantBlockUnlessYouControl subtypes => .cantBlockUnless subtypes
  | .cantBeBlockedExceptBy n => .cantBeBlockedExcept n
  | .enchantedIsOnlySubtypeCantAttackOrBlock subtype =>
    .enchantedOnlySubtypeCantAttackOrBlock subtype
  | .powerEqualCardsInHand => .cardsInHandPower
  | .equippedCreatureHasKeywords k => .hostKeywords "Equipped creature" k 0 0
  | .enchantedCreatureGetsAndHas p t k => .hostKeywords "Enchanted creature" k p t
  | .cantBeBlockedByTokens => .cantBeBlockedByTokens
  | .powerEqualCreaturesYouControl => .creaturesYouControlPower
  | .armiesYouControlHaveTrample => .youControlSubtypeTrample "Army"
  | .creaturesYouControlGet p t => .teamPump p t false false
  | .hasteIfYouControlOtherSubtype subtype => .hasteIfOtherSubtype subtype
  | .cantAttackUnlessYouControlNOther n subtype => .cantAttackUnlessNOther n subtype
  | .legendaryCreaturesGetAndWard p t w => .legendaryTeamPumpWard p t w
  | .nonlegendaryCreaturesGet p t => .teamPump p t false true
  | .equippedCreatureGetsAndHas p t k => .hostKeywords "Equipped creature" k p t
  | .equippedCreatureGetsAndWard p t w => .hostGetsAndWard "Equipped creature" p t w
  | .creaturesYouControlWithPlusOneHaveMenace => .creaturesWithPlusOneHaveMenace
  | .lifelinkIfYouControlOtherSubtype subtype => .lifelinkIfOtherSubtype subtype
  | .thresholdGets p t => .thresholdGets p t
  | .cantBeBlockedByPowerAtMost n => .cantBeBlockedByPowerAtMost n
  | .equippedCreaturesHaveKeywordsDuringYourTurn k =>
    .equippedTeamKeywordsDuringYourTurn k
  | .getsAndHasIfEnduringStory p t k => .selfIfEnduringStory p t k
  | .creaturesYouControlGetIfEnduringStory p t => .teamIfEnduringStory p t
  | .doesntUntapUnlessEnduringStory => .doesntUntapUnlessEnduringStory
  | .artifactsAndCreaturesHaveWardIfEnduringStory w => .teamWardIfEnduringStory w
  | .creaturesCantAttackYouUnlessPayIfEnduringStory n => .attackTaxIfEnduringStory n
  | .otherSubtypeHaveTapAddOneOf subtypes mana =>
    .otherSubtypeTapAddOneOf subtypes mana
  | .cantBeBlockedByPowerAtLeast n => .cantBeBlockedByPowerAtLeast n
  | .equippedCreatureHasKeywordsAndCantBeBlocked k =>
    .equippedKeywordsAndUnblockable k
  | .equipAbilitiesTargetingThisCostLess n => .equipTargetingThisCostLess n
  | .firstEquipFreeIfEnduringStory => .firstEquipFreeIfEnduringStory
  | .chosenTypeCreaturesGet p t => .chosenTypePump p t
  | .instantSorceryCostReductionEqualEquippedPower =>
    .instantSorceryCostReductionEqualEquippedPower
  | .otherSubtypeGetPowerPerArtifactToken subtype =>
    .otherSubtypePowerPerArtifactToken subtype
  | .extraTriggerIfEnduringStorySubtype subtype =>
    .extraTriggerIfEnduringStorySubtype subtype
  | .extraTriggerAnotherYouControl subtypes includeBattles =>
    .extraTriggerAnotherYouControl subtypes includeBattles
  | .enchantedLosesAbilitiesDoesntUntap => .enchantedLosesAbilitiesDoesntUntap
  | .equippedHexproofUnblockableDuringYourTurn =>
    .equippedHexproofUnblockableDuringYourTurn
  | .equippedTriggersAgain => .equippedTriggersAgain
  | .equippedFirstStrikePlusPerInstantSorcery =>
    .equippedFirstStrikePlusPerInstantSorcery
  | .powerPerFatGraveyard n => .powerPerFatGraveyard n
  | .exileOppDeathCreateWolf => .exileOppDeathCreateWolf
  | .copyActivatedFromGySubtype subtype => .copyActivatedFromGySubtype subtype
  | .equippedGetsTrampleAndCombatTreasures p t =>
    .equippedGetsTrampleAndCombatTreasures p t
  | .wardDiscardEnchantmentInstantOrSorcery =>
    .wardDiscardEnchantmentInstantOrSorcery
  | .wardSacrificeLegendary => .wardSacrificeLegendary
  | .creaturesYouControlOfSubtypeGet subtype p t =>
    .teamPumpSubtype subtype p t
  | .youAndOtherSubtypeHaveHexproofIfShield subtype =>
    .youAndOtherSubtypeHexproofIfShield subtype
  | .opponentsCantCastOnYourTurn => .opponentsCantCastOnYourTurn
  | .subtypeSpellsCostLess subtype n => .subtypeSpellsCostLess subtype n
  | .cantBeBlockedIfPowerAtMost n => .cantBeBlockedIfPowerAtMost n
  | .preventAllDamageToThis => .preventAllDamageToThis
  | .noMaximumHandSize => .noMaximumHandSize
  | .maximumHandSize n => .maximumHandSize n
  | .powerEqualSubtypeYouControl subtype => .powerEqualSubtype subtype
  | .powerEqualLegendaryCreaturesYouControl => .powerEqualLegendaryCreatures
  | .typeSpellsCostLess ty n => .typeSpellsCostLess ty n
  | .improvise => .improvise
  | .noncreatureSpellsHaveImprovise => .noncreatureSpellsHaveImprovise
  | .extort => .extort
  | .attackingTokensHave k => .attackingTokensHave k
  | .hexproofIfPlusOneThisTurn => .hexproofIfPlusOneThisTurn
  | .mayPlayLandsFromGraveyard => .mayPlayLandsFromGraveyard
  | .flashIfOpponentCastThisTurn => .flashIfOpponentCastThisTurn
  | .wardDiscardOrPay n => .wardDiscardOrPay n
  | .wardPoisonCounters n => .wardPoisonCounters n
  | .attacksEachCombatIfAble => .attacksEachCombatIfAble
  | .instantSorceryCostLessEqualPower => .instantSorceryCostLessEqualPower
  | .extraPowerUpActivation => .extraPowerUpActivation
  | .otherPowerUpCostsLess n => .otherPowerUpCostsLess n
  | .activateCreaturesAsThoughHaste => .activateCreaturesAsThoughHaste
  | .extraCounterOnPermanents => .extraCounterOnPermanents
  | .mayBeginOnBattlefield => .mayBeginOnBattlefield
  | .enchantedCreatureHasWard w => .enchantedHasWard w
  | .equippedCreatureGetsHasAndWard p t k w => .equippedGetsHasAndWard p t k w
  | .creaturesWithPlusOneHave k => .creaturesWithPlusOneHave k
  | .opponentsCreaturesGet p t => .opponentsCreaturesGet p t
  | .getsPowerPerOtherArtifact p => .getsPowerPerOtherArtifact p
  | .getsPowerPerAttachedEquipment p => .getsPowerPerAttachedEquipment p
  | .getsIfGyCreatureCards min p t => .getsIfGyCreatureCards min p t
  | .indestructibleIfArtifactCreatureOrPlan =>
    .indestructibleIfArtifactCreatureOrPlan
  | .flyingIfPlusOneThisTurn => .flyingIfPlusOneThisTurn
  | .flyingCantAttackYouOrBlockYours => .flyingCantAttackYouOrBlockYours
  | .extraDrawOnConnive => .extraDrawOnConnive
  | .noncombatDamagePlusSourcePower => .noncombatDamagePlusSourcePower
  | .equippedDealsDoubleDamage => .equippedDealsDoubleDamage
  | .healOtherDamageWhenDealt => .healOtherDamageWhenDealt
  | .entersWithXPlusOne => .entersWithXPlusOne
  | .enchantedCreatureGetsHasAndTypes p t k types =>
    .enchantedGetsHasAndTypes p t k types
  | .enchantedLosesAbilitiesCantUntap => .enchantedLosesAbilitiesCantUntap
  | .enchantedCreatureGetsHasAndWard p t k w =>
    .enchantedGetsHasAndWard p t k w
  | .getsAndAllTypesIfGyCreatureCards min p t =>
    .getsAndAllTypesIfGyCreatureCards min p t
  | .sneak cost => .sneak cost
  | .boast => .boast

/-- Oracle-style reminder from `shape`, so a new constructor only updates that
table. -/
def toNotation (ab : StaticAbility) : String :=
  match ab.shape with
  | .lordTrample subtypes =>
    s!"Other {joinedSubtypes subtypes pluralSubtype} you control have trample."
  | .lordPump subtypes p t =>
    if subtypes.isEmpty then
      s!"Other creatures you control get {signedStat p}/{signedStat t}."
    else
      s!"Other {joinedSubtypes subtypes} creatures you control get {signedStat p}/{signedStat t}."
  | .hostGets host p t => hostGetsPhrase host p t
  | .landsYouControlPT =>
    "This creature's power and toughness are each equal to the number of lands you control."
  | .cantBlockUnless subtypes =>
    match subtypes.toList with
    | [] => "This creature can't block."
    | xs =>
      s!"This creature can't block unless you control a {String.intercalate " or " xs}."
  | .cantBeBlockedExcept n =>
    s!"This creature can't be blocked except by {englishNumber n} or more creatures."
  | .enchantedOnlySubtypeCantAttackOrBlock subtype =>
    s!"Enchanted creature is a {subtype} and can't attack or block."
  | .cardsInHandPower =>
    "This power is equal to the number of cards in your hand."
  | .hostKeywords host k p t =>
    let kw := k.joinedAnd
    if p == 0 && t == 0 then
      s!"{host} has {kw}."
    else
      s!"{host} gets {signedStat p}/{signedStat t} and has {kw}."
  | .cantBeBlockedByTokens =>
    "This creature can't be blocked by tokens."
  | .creaturesYouControlPower =>
    "This power is equal to the number of creatures you control."
  | .youControlSubtypeTrample subtype =>
    s!"{pluralSubtype subtype} you control have trample."
  | .teamPump p t legendaryOnly nonlegendaryOnly =>
    let who :=
      if legendaryOnly then "Legendary creatures you control"
      else if nonlegendaryOnly then "Nonlegendary creatures you control"
      else "Creatures you control"
    s!"{who} get {signedStat p}/{signedStat t}."
  | .hasteIfOtherSubtype subtype =>
    s!"This creature has haste as long as you control another {subtype}."
  | .cantAttackUnlessNOther n subtype =>
    s!"This creature can't attack unless you control {englishNumber n} or more other {pluralSubtype subtype}."
  | .legendaryTeamPumpWard p t w =>
    s!"Legendary creatures you control get {signedStat p}/{signedStat t} and have ward \{{w}}."
  | .hostGetsAndWard host p t w =>
    s!"{host} gets {signedStat p}/{signedStat t} and has ward \{{w}}."
  | .creaturesWithPlusOneHaveMenace =>
    "Each creature you control with a +1/+1 counter on it has menace."
  | .lifelinkIfOtherSubtype subtype =>
    s!"This creature has lifelink as long as you control another {subtype}."
  | .thresholdGets p t =>
    s!"This creature gets {signedStat p}/{signedStat t} as long as there are seven or more cards in your graveyard."
  | .cantBeBlockedByPowerAtMost n =>
    s!"This creature can't be blocked by creatures with power {n} or less."
  | .equippedTeamKeywordsDuringYourTurn k =>
    let kw :=
      if k.firstStrike && k.vigilance then "first strike and vigilance"
      else k.joinedAnd
    s!"During your turn, creatures you control that are equipped have {kw}."
  | .selfIfEnduringStory p t k =>
    let kw := k.joinedAnd
    if p == 0 && t == 0 then
      s!"As long as you have an enduring story, this has {kw}."
    else if k.toList.isEmpty then
      s!"As long as you have an enduring story, this gets {signedStat p}/{signedStat t}."
    else
      s!"As long as you have an enduring story, this gets {signedStat p}/{signedStat t} and has {kw}."
  | .teamIfEnduringStory p t =>
    s!"As long as you have an enduring story, creatures you control get {signedStat p}/{signedStat t}."
  | .doesntUntapUnlessEnduringStory =>
    "This doesn't untap during your untap step unless you have an enduring story."
  | .teamWardIfEnduringStory w =>
    s!"As long as you have an enduring story, artifacts and creatures you control have ward \{{w}}."
  | .attackTaxIfEnduringStory n =>
    s!"As long as you have an enduring story, creatures can't attack you unless their controller pays \{{n}} for each of those creatures."
  | .otherSubtypeTapAddOneOf subtypes mana =>
    let add := manaSymbolsText mana " or "
    s!"Other {joinedSubtypes subtypes pluralSubtype} you control have \"\{T}: Add {add}.\""
  | .cantBeBlockedByPowerAtLeast n =>
    s!"This creature can't be blocked by creatures with power {n} or greater."
  | .equippedKeywordsAndUnblockable k =>
    s!"Equipped creature has {k.joinedAnd} and can't be blocked."
  | .equipTargetingThisCostLess n =>
    s!"Equip abilities you activate that target this creature cost \{{n}} less to activate."
  | .firstEquipFreeIfEnduringStory =>
    "As long as you have an enduring story, you may pay {0} rather than pay the equip cost of the first equip ability you activate each turn."
  | .chosenTypePump p t =>
    s!"Creatures you control of the chosen type get {signedStat p}/{signedStat t}."
  | .instantSorceryCostReductionEqualEquippedPower =>
    "Instant and sorcery spells you cast cost {X} less to cast, where X is equipped creature's power."
  | .otherSubtypePowerPerArtifactToken subtype =>
    s!"Other {pluralSubtype subtype} you control get +1/+0 for each artifact token you control."
  | .extraTriggerIfEnduringStorySubtype subtype =>
    s!"As long as you have an enduring story, if a triggered ability of a {subtype} you control triggers, that ability triggers an additional time."
  | .extraTriggerAnotherYouControl subtypes includeBattles =>
    let parts :=
      subtypes.toList ++ (if includeBattles then ["battle"] else [])
    let joined :=
      match parts with
      | [a] => a
      | [a, b] => s!"{a} or {b}"
      | xs => String.intercalate ", " xs
    s!"If a triggered ability of another {joined} you control triggers, that ability triggers an additional time."
  | .enchantedLosesAbilitiesDoesntUntap =>
    "Enchanted creature loses all abilities and doesn't untap during its controller's untap step."
  | .equippedHexproofUnblockableDuringYourTurn =>
    "During your turn, equipped creature has hexproof and can't be blocked."
  | .equippedTriggersAgain =>
    "If a triggered ability of equipped creature triggers, that ability triggers an additional time."
  | .equippedFirstStrikePlusPerInstantSorcery =>
    "Equipped creature has first strike and gets +1/+0 for each instant and sorcery card in your graveyard."
  | .powerPerFatGraveyard n =>
    s!"This creature gets {signedStat n}/+0 for each graveyard with seven or more cards in it."
  | .exileOppDeathCreateWolf =>
    "If a creature an opponent controls would die, exile it instead. When you do, create a 2/2 green Wolf creature token."
  | .copyActivatedFromGySubtype subtype =>
    s!"This has all activated abilities of all {subtype} cards in your graveyard."
  | .equippedGetsTrampleAndCombatTreasures p t =>
    s!"Equipped creature gets {signedStat p}/{signedStat t} and has trample and \"Whenever this creature deals combat damage to a player or planeswalker, create that many Treasure tokens.\""
  | .wardDiscardEnchantmentInstantOrSorcery =>
    "Ward—Discard an enchantment, instant, or sorcery card."
  | .wardSacrificeLegendary =>
    "Ward—Sacrifice a legendary artifact or legendary creature."
  | .teamPumpSubtype subtype p t =>
    s!"{pluralSubtype subtype} you control get {signedStat p}/{signedStat t}."
  | .youAndOtherSubtypeHexproofIfShield subtype =>
    s!"As long as this has a shield counter on it, you and other {pluralSubtype subtype} you control have hexproof."
  | .opponentsCantCastOnYourTurn =>
    "Your opponents can't cast spells during your turn."
  | .subtypeSpellsCostLess subtype n =>
    s!"{subtype} spells you cast cost \{{n}} less to cast."
  | .cantBeBlockedIfPowerAtMost n =>
    s!"This creature can't be blocked if its power is {n} or less."
  | .preventAllDamageToThis =>
    "Prevent all damage that would be dealt to this."
  | .noMaximumHandSize =>
    "You have no maximum hand size."
  | .maximumHandSize n =>
    s!"Your maximum hand size is {n}."
  | .powerEqualSubtype subtype =>
    s!"This creature's power is equal to the number of {pluralSubtype subtype} you control."
  | .powerEqualLegendaryCreatures =>
    "This creature's power is equal to the number of legendary creatures you control."
  | .typeSpellsCostLess ty n =>
    s!"{ty} spells you cast cost \{{n}} less to cast."
  | .improvise =>
    "Improvise"
  | .noncreatureSpellsHaveImprovise =>
    "Noncreature spells you cast have improvise."
  | .extort =>
    "Extort"
  | .attackingTokensHave k =>
    s!"Attacking creature tokens you control have {k}."
  | .hexproofIfPlusOneThisTurn =>
    "Each creature you control that you've put one or more +1/+1 counters on this turn has hexproof."
  | .mayPlayLandsFromGraveyard =>
    "You may play lands from your graveyard."
  | .flashIfOpponentCastThisTurn =>
    "As long as an opponent has cast a spell this turn, you may cast spells as though they had flash."
  | .wardDiscardOrPay n =>
    s!"Ward—Discard a card or pay \{{n}}."
  | .wardPoisonCounters n =>
    s!"Ward—Get {englishNumber n} poison counters."
  | .attacksEachCombatIfAble =>
    "This creature attacks each combat if able."
  | .instantSorceryCostLessEqualPower =>
    "Instant and sorcery spells you cast with mana value 4 or greater cost {X} less to cast, where X is this creature's power."
  | .extraPowerUpActivation =>
    "Each power-up ability of permanents you control can be activated an additional time."
  | .otherPowerUpCostsLess n =>
    s!"Power-up abilities of other creatures you control cost \{{n}} less to activate."
  | .activateCreaturesAsThoughHaste =>
    "You may activate abilities of creatures you control as though those creatures had haste."
  | .extraCounterOnPermanents =>
    "If you would put one or more counters on a permanent you control, put that many plus one of each of those kinds of counters on that permanent instead."
  | .mayBeginOnBattlefield =>
    "If this card is in your opening hand, you may begin the game with it on the battlefield."
  | .enchantedHasWard w =>
    s!"Enchanted creature has ward \{{w}}."
  | .equippedGetsHasAndWard p t k w =>
    s!"Equipped creature gets {signedStat p}/{signedStat t} and has {k} and ward \{{w}}."
  | .creaturesWithPlusOneHave k =>
    s!"Creatures you control with +1/+1 counters on them have {k}."
  | .opponentsCreaturesGet p t =>
    s!"Creatures your opponents control get {signedStat p}/{signedStat t}."
  | .getsPowerPerOtherArtifact p =>
    s!"This creature gets {signedStat p}/+0 for each other artifact you control."
  | .getsPowerPerAttachedEquipment p =>
    s!"This creature gets {signedStat p}/+0 for each Equipment attached to it."
  | .getsIfGyCreatureCards min p t =>
    s!"As long as there are {min} or more creature cards in your graveyard, this creature gets {signedStat p}/{signedStat t}."
  | .indestructibleIfArtifactCreatureOrPlan =>
    "As long as you control an artifact creature or a Plan, this has indestructible."
  | .flyingIfPlusOneThisTurn =>
    "As long as you've put one or more +1/+1 counters on this creature this turn, it has flying."
  | .flyingCantAttackYouOrBlockYours =>
    "Creatures with flying can't attack you or block creatures you control."
  | .extraDrawOnConnive =>
    "If a creature you control would connive, instead you draw a card, then that creature connives."
  | .noncombatDamagePlusSourcePower =>
    "If a source you control would deal noncombat damage to an opponent or a permanent an opponent controls, instead it deals that much damage plus X, where X is this creature's power."
  | .equippedDealsDoubleDamage =>
    "Double all damage equipped creature would deal."
  | .healOtherDamageWhenDealt =>
    "If damage would be dealt to this creature, instead that damage is dealt, but all other damage already dealt to it is healed."
  | .entersWithXPlusOne =>
    "This enters with X +1/+1 counters on it."
  | .enchantedGetsHasAndTypes p t k types =>
    let kw :=
      if k.firstStrike && k.vigilance then "first strike and vigilance"
      else k.joinedAnd
    let extra :=
      if types.isEmpty then ""
      else s!", and is a {String.intercalate " " types.toList} in addition to its other types"
    s!"Enchanted creature gets {signedStat p}/{signedStat t}, has {kw}{extra}."
  | .enchantedLosesAbilitiesCantUntap =>
    "Enchanted creature loses all abilities and can't become untapped."
  | .enchantedGetsHasAndWard p t k w =>
    s!"Enchanted creature gets {signedStat p}/{signedStat t} and has {k} and ward \{{w}}."
  | .getsAndAllTypesIfGyCreatureCards min p t =>
    s!"As long as there are {min} or more creature cards in your graveyard, this creature gets {signedStat p}/{signedStat t} and is all creature types."
  | .sneak cost =>
    s!"Sneak {cost}"
  | .boast =>
    "Boast — Exile any number of black cards from your graveyard with fifteen or more black mana symbols among their mana costs: Copy those exiled cards. You may cast up to three of the copies without paying their mana costs."

instance : ToString StaticAbility where
  toString := toNotation

/-- Lord +P/+T this ability grants other matching creatures, if any. -/
def lordPump? (ab : StaticAbility) : Option (Array String × Int × Int) :=
  ab.shape.spec.lordPump

/-- Subtypes this ability grants trample to, if any. -/
def trampleSubtypes? (ab : StaticAbility) : Option (Array String) :=
  ab.shape.spec.trampleSubtypes

/-- Continuous +P/+T this ability grants its enchanted or equipped host
(CR 613.3c). Other static abilities contribute `(0, 0)` here. -/
def hostStatBonus (ab : StaticAbility) : Int × Int :=
  ab.shape.spec.hostBonus

/-- True for the lands-you-control P/T characteristic-defining ability. -/
def isLandsYouControlPT (ab : StaticAbility) : Bool :=
  ab.shape.spec.landsYouControlPT

/-- Subtypes required to declare a blocker, if this ability restricts blocking. -/
def cantBlockUnless? (ab : StaticAbility) : Option (Array String) :=
  ab.shape.spec.cantBlockUnless

/-- Minimum number of blockers required, if this ability restricts blocking. -/
def cantBeBlockedExcept? (ab : StaticAbility) : Option Nat :=
  ab.shape.spec.cantBeBlockedExcept

/-- Enchanted-only subtype that also prevents attacking and blocking. -/
def enchantedOnlySubtype? (ab : StaticAbility) : Option String :=
  ab.shape.spec.enchantedOnlySubtype

/-- True for the cards-in-hand power characteristic-defining ability. -/
def isCardsInHandPower (ab : StaticAbility) : Bool :=
  ab.shape.spec.cardsInHandPower

/-- Keywords this ability grants its enchanted or equipped host. -/
def hostKeywords (ab : StaticAbility) : Keywords :=
  ab.shape.spec.hostKeywords

/-- True when this creature can't be blocked by tokens. -/
def blocksTokens (ab : StaticAbility) : Bool :=
  ab.shape.spec.cantBeBlockedByTokens

/-- True for the creatures-you-control power characteristic-defining ability. -/
def isCreaturesYouControlPower (ab : StaticAbility) : Bool :=
  ab.shape.spec.creaturesYouControlPower

/-- True when this lord pump also applies to the source. -/
def lordIncludesSelf (ab : StaticAbility) : Bool :=
  ab.shape.spec.lordIncludesSelf

/-- True when this lord pump applies only to legendary creatures. -/
def lordLegendaryOnly (ab : StaticAbility) : Bool :=
  ab.shape.spec.lordLegendaryOnly

/-- True when this lord pump applies only to nonlegendary creatures. -/
def lordNonlegendaryOnly (ab : StaticAbility) : Bool :=
  ab.shape.spec.lordNonlegendaryOnly

/-- Ward cost this ability grants matching creatures, if any. -/
def grantedWard? (ab : StaticAbility) : Option Nat :=
  ab.shape.spec.grantedWard

/-- Subtype that grants this creature haste while another is controlled. -/
def hasteIfOtherSubtype? (ab : StaticAbility) : Option String :=
  ab.shape.spec.hasteIfOtherSubtype

/-- Attack restriction: need `n` other permanents of this subtype. -/
def cantAttackUnlessNOther? (ab : StaticAbility) : Option (Nat × String) :=
  ab.shape.spec.cantAttackUnlessNOther

def creaturesWithPlusOneHaveMenace (ab : StaticAbility) : Bool :=
  ab.shape.spec.creaturesWithPlusOneHaveMenace

def lifelinkIfOtherSubtype? (ab : StaticAbility) : Option String :=
  ab.shape.spec.lifelinkIfOtherSubtype

def thresholdGets? (ab : StaticAbility) : Option (Int × Int) :=
  ab.shape.spec.thresholdGets

def cantBeBlockedByPowerAtMost? (ab : StaticAbility) : Option Int :=
  ab.shape.spec.cantBeBlockedByPowerAtMost

/-- Can't be blocked by creatures with power at least this. -/
def cantBeBlockedByPowerAtLeast? (ab : StaticAbility) : Option Int :=
  ab.shape.spec.cantBeBlockedByPowerAtLeast

/-- This creature can't be blocked if its power is at most this. -/
def cantBeBlockedIfPowerAtMost? (ab : StaticAbility) : Option Int :=
  ab.shape.spec.cantBeBlockedIfPowerAtMost

/-- True when this Equipment also makes its host unblockable. -/
def equippedCantBeBlocked (ab : StaticAbility) : Bool :=
  ab.shape.spec.equippedCantBeBlocked

def equippedTeamKeywordsDuringYourTurn (ab : StaticAbility) : Keywords :=
  ab.shape.spec.equippedTeamKeywordsDuringYourTurn

def selfIfEnduringStory? (ab : StaticAbility) : Option (Int × Int × Keywords) :=
  ab.shape.spec.selfIfEnduringStory

def teamIfEnduringStory? (ab : StaticAbility) : Option (Int × Int) :=
  ab.shape.spec.teamIfEnduringStory

def doesntUntapUnlessEnduringStory? (ab : StaticAbility) : Bool :=
  ab.shape.spec.doesntUntapUnlessEnduringStory

def teamWardIfEnduringStory? (ab : StaticAbility) : Option Nat :=
  ab.shape.spec.teamWardIfEnduringStory

def attackTaxIfEnduringStory? (ab : StaticAbility) : Option Nat :=
  ab.shape.spec.attackTaxIfEnduringStory

end StaticAbility

end Mtg.Engine
