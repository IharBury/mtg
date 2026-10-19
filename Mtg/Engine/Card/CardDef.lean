import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.Saga
import Mtg.Engine.Card.StaticAbility
import Mtg.Engine.Card.TriggeredAbility

/-!
# Card definitions (CR 108, 109.3, section 2)

Printed Oracle characteristics: `CardDef`, the `AdventureFace` of
adventurer cards, and per-card mana-ability storage.
-/

namespace Mtg.Engine

/-- A `{T}: Add {M} for each [subtype] you control` mana ability (CR 106.4 / 605). -/
structure TapAddForEach where
  mana : ManaType
  subtype : String
deriving Repr, Inhabited, BEq

namespace TapAddForEach

def toNotation (a : TapAddForEach) : String :=
  s!"\{T}: Add \{{a.mana.letter}} for each {a.subtype} you control"

instance : ToString TapAddForEach where
  toString := toNotation

end TapAddForEach

/-- Alternative characteristics of an adventurer card while it is a spell
cast as an Adventure (CR 715.2). -/
structure AdventureFace where
  name : String
  manaCost : ManaCost := ManaCost.empty
  types : Array CardType := #[.sorcery]
  subtypes : Array Subtype := #["Adventure"]
  spellEffect : Option Effect := none
  /-- Additional cost: sacrifice a creature. -/
  additionalCostSacrificeCreature : Bool := false
  /-- Rules lines of this face that are not a modeled spell effect. -/
  extraLines : Array String := #[]
  /-- Empower Jace N on this alternate face. -/
  empowerJace : Option Nat := none
deriving Repr, Inhabited, BEq

/-- Replacement rule for whether a permanent enters the battlefield tapped (CR 614.1c). -/
inductive EntersTappedRule where
  | untapped
  | always
  | unlessLegendary
  | unlessEquipment
  | unlessPlaneswalker
  | unlessTwoOtherLands
  | unlessPayLife (life : Nat)
  | unlessAnySubtype (subtypes : Array String)
  | unlessNBasics (n : Nat)
  | unlessOppLands (n : Nat)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Counters a permanent enters the battlefield with (CR 614.1c). -/
inductive EntersWithCounters where
  | none
  | plusOne (n : Nat)
  | shield (n : Nat)
  | indestructible
  | hopePerCreature
deriving Repr, Inhabited, BEq, DecidableEq

/-- Choice made as a permanent enters the battlefield (CR 614.12). -/
inductive AsEntersChoice where
  | none
  | creatureType
  | oddEven
  | cardType
  | marduOrJeskai
deriving Repr, Inhabited, BEq, DecidableEq

/-- Printed spell cost reduction (CR 601.2f). -/
inductive SpellCostReduction where
  | none
  | ifCreatureDied (n : Nat)
  | ifTargetDamaged (n : Nat)
  | ifTargetTapped (n : Nat)
  | ifTargetAttackingNontoken (n : Nat)
  | ifTargetAttacking (n : Nat)
  | ifYouControl (n : Nat) (subtype : String)
  | ifGyCreaturesAtLeast (min : Nat) (n : Nat)
  | equalFlyingPower
  | greatestPower
  | greatestToughness
  | equalOppArtifacts
deriving Repr, Inhabited, BEq, DecidableEq

/-- Printed additional cost to cast a spell (CR 601.2b / 118.8). -/
inductive SpellAdditionalCost where
  | none
  | sacrificeCreature
  | sacrificeArtifactOrCreature (orPayGeneric : Option Nat := none)
  | sacrificeCreatureOrPlaneswalkerOrPay (generic : Nat)
  | discardOrPay (generic : Nat)
  | beholdOrPay (quality : String) (generic : Nat)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Printed `{T}: Add …` mana ability beyond simple single-symbol `tapAddMana`
(CR 605.1a). -/
inductive TapManaAbility where
  | none
  | oneOf (types : Array ManaType)
  | oneOfIfEnteredOrBasic (types : Array ManaType)
  | oneOfDealsDamage (types : Array ManaType) (damage : Nat)
  | payLifeOneOf (life : Nat) (types : Array ManaType)
  | together (types : Array ManaType)
  | twoAmong (types : Array ManaType)
  | filter (cost : ManaCost) (types : Array ManaType)
  | forEach (entries : Array TapAddForEach)
  | colorlessPerSubtype (subtype : String)
  | anyColor
  | sacrificeAnyColor
  | anyColorEqualToPower
  | anyColorForInstantOrSorcery
  | anyColorForLegendary
  | anyColorAmongLegendaries
  | chosenColorPerDifferentPower
  | restricted (types : Array ManaType) (restriction : String)
  | commanderIdentity (scryCreature : Bool := false)
  | oppCouldProduce
  | youCouldProduce
deriving Repr, Inhabited, BEq

/-- Mode-selection rule for a modal spell (CR 700.2). -/
inductive ModalRule where
  | chooseOne
  | chooseOneOrBoth
  | chooseTwoIfYouControl (subtype : String)
  | chooseBothIfTeamwork
deriving Repr, Inhabited, BEq, DecidableEq

/-- Permission to look at or play/cast cards from the top of your library
(CR 401.5 / 601.3). -/
inductive TopOfLibraryRule where
  | none
  | lookAnytime
  | playLands
  | castCreatures
  | elvenChorus
  | grantCreaturesTapAnyColor
deriving Repr, Inhabited, BEq, DecidableEq

/-- Continuous or replacement static rule on a card (CR 604 / 613 / 614). -/
inductive CardStaticRule where
  | none
  | foodAlsoCreatesTreasure
  | othersEnterWithPlusOneEqualToughness
  | powerPerMountain (n : Nat)
  | extraLandIfOtherSubtype (subtype : String)
  | tokenDoubling (andDrawTwo : Bool := false)
  | drawTwoExceptFirstDrawStep
  | exileOppCreaturesInstead
  | firstCreatureDiscount (costReduction : Nat) (hasFlash : Bool)
  | hexproofIndestructibleIfLore (minLore : Nat)
  | costReductionNotFromHand (n : Nat)
  | grantLandsTapAnyColor
  | freeCastIfControlCommander
  | opponentsCantGainLife
  | cantLoseAndOpponentsCantWin (andNoMinusCounters : Bool := false)
  | creaturesCantGetMinusCounters
  | powerPerUnspentMana (andColorless : Bool := false)
  | unspentManaBecomesColorless
  | eminenceSphinxReduction (n : Nat)
  | protectionFromChosenCardType
  | corruptedToxicLifelink
  | grantTeamPlusTwoFlying
deriving Repr, Inhabited, BEq, DecidableEq

/-- Optional or alternative casting option on a card (CR 118.8 / 118.9 / 702). -/
inductive SpellCastOption where
  | none
  | flashback (cost : ManaCost) (discard : Bool := false)
  | kicker (cost : ManaCost)
  | giftTreasure
  | teamwork (minPower : Nat)
  | morph (cost : ManaCost)
  | impending (counters : Nat) (cost : ManaCost)
  | affinity (subtype : String)
  | cascade (n : Nat)
deriving Repr, Inhabited, BEq

/-- Casting permission, restriction, or counterability rule on a card
(CR 601.2 / 601.3 / 608.2a). -/
inductive CastPermissionRule where
  | normal
  | cantBeCountered
  | flashIfYouControl (subtype : String)
  | castExiledWithSevenInGraveyard
  | castOnlyIfGraveyardAtLeast (min : Nat)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Parameterized keyword or deck-building / blocking rule on a card
(CR 702 / 100.2a / 903.3a). -/
inductive CardKeywordRule where
  | none
  | ward (n : Nat)
  | crew (n : Nat)
  | prowess (n : Nat)
  | protectionFromColors (colors : Array Color)
  | cycling (cost : ManaCost)
  | daybound
  | toxic (n : Nat) (cantBlock : Bool := false)
  | cantBlock
  | anyNumberInDeck
  | canBeCommander
deriving Repr, Inhabited, BEq

set_option maxRecDepth 1024 in
/-- Printed (Oracle) characteristics of a card. -/
structure CardDef where
  name : String
  manaCost : ManaCost := ManaCost.empty
  types : Array CardType
  subtypes : Array Subtype := #[]
  supertypes : Array Supertype := #[]
  power : Option Int := none
  toughness : Option Int := none
  /-- Printed power includes a star added to `power` (CR 208.2).
  A bare `*` leaves `power` empty. `1+*` and `*+1` are `some 1`.
  When that star can't be determined it counts as 0, so the power is
  `power.getD 0`: `*` is 0 and `1+*` is 1 (CR 208.2a). -/
  powerStar : Bool := false
  /-- Printed toughness includes a star added to `toughness` (CR 208.2).
  See `powerStar`. -/
  toughnessStar : Bool := false
  /-- Printed loyalty number (CR 209.1). While this planeswalker is not on
  the battlefield, its loyalty is this number. It enters the battlefield
  with that many loyalty counters. -/
  loyalty : Option Int := none
  /-- Printed defense number (CR 210.1). While this battle is not on
  the battlefield, its defense is this number. It enters the battlefield
  with that many defense counters. -/
  defense : Option Nat := none
  /-- Printed hand modifier (CR 211.1). The lower-left corner of a vanguard:
  a number preceded by a plus sign, a number preceded by a minus sign, or
  zero. It modifies its owner's starting hand size and maximum hand size. -/
  handModifier : Option Int := none
  /-- Printed life modifier (CR 212.1). The lower-right corner of a vanguard:
  a number preceded by a plus sign, a number preceded by a minus sign, or
  zero. It modifies its owner's starting life total. -/
  lifeModifier : Option Int := none
  /-- Explicit color indicator, if any (CR 107.13 / 202.2). -/
  colorIndicator : Option ColorSet := none
  keywords : Keywords := Keywords.none
  /-- Parameterized keyword or deck-building / blocking rule (CR 702 / 100.2a / 903.3a). -/
  keywordRule : CardKeywordRule := .none
  spellEffect : Option Effect := none
  /-- Additional cost to cast this spell (CR 601.2b / 118.8). -/
  additionalCost : SpellAdditionalCost := .none
  /-- Cost reduction on this spell (CR 601.2f). -/
  spellCostReduction : SpellCostReduction := .none
  /-- Optional or alternative casting option on this card (CR 118.8 / 118.9 / 702). -/
  castOption : SpellCastOption := .none
  /-- Casting permission, restriction, or counterability rule (CR 601.2 / 601.3 / 608.2a). -/
  castPermission : CastPermissionRule := .normal
  /-- Modes of a “Choose one” spell (CR 700.2). Nonempty means the spell is modal. -/
  spellModes : Array Effect := #[]
  /-- Mode-selection rule for a modal spell (CR 700.2). -/
  modalRule : ModalRule := .chooseOne
  /-- Modes of this card's modal triggered ability (“When this creature
  enters, choose one —”), chosen as it is put on the stack (CR 603.3c). -/
  fraTriggerModes : Array Effect := #[]
  /-- Additional `{T}: Add _` abilities that are not implied by basic land types. -/
  tapAddMana : Array ManaType := #[]
  /-- `{T}: Add …` mana ability beyond simple single-symbol `tapAddMana` (CR 605.1a). -/
  tapManaAbility : TapManaAbility := .none
  /-- Replacement rule for whether this permanent enters tapped (CR 614.1c). -/
  entersTappedRule : EntersTappedRule := .untapped
  /-- Counters this permanent enters the battlefield with (CR 614.1c). -/
  entersWithCounters : EntersWithCounters := .none
  /-- Choice made as this permanent enters the battlefield (CR 614.12). -/
  asEntersChoose : AsEntersChoice := .none
  /-- This object is a token (CR 111). -/
  isToken : Bool := false
  /-- Abilities planeswalkers you control have (“Planeswalkers you control
  have …”). -/
  planeswalkersYouControlHave : Array ActivatedAbility := #[]
  /-- Printed Saga chapters (CR 714). -/
  saga : Option SagaDef := none
  /-- Non-mana activated abilities (CR 602). `{T}: Add` mana abilities are
  `tapAddMana` / `tapManaAbility` / basic land types instead. -/
  activatedAbilities : Array ActivatedAbility := #[]
  /-- Static abilities other than printed keywords (CR 604). -/
  staticAbilities : Array StaticAbility := #[]
  /-- Triggered abilities (CR 603). -/
  triggeredAbilities : Array TriggeredAbility := #[]
  /-- Permission to look at or play/cast cards from the top of your library
  (CR 401.5 / 601.3). -/
  topOfLibraryRule : TopOfLibraryRule := .none
  /-- Continuous or replacement static rule on this card (CR 604 / 613 / 614). -/
  staticRule : CardStaticRule := .none
  /-- Alternative characteristics used when this card is cast as an Adventure
  (CR 715). -/
  adventure : Option AdventureFace := none
  /-- Back face of a modal double-faced card that can transform. -/
  otherFace : Option CardDef := none
  /-- Empower Jace N on this spell (Reality Fracture). When the spell
  resolves, put N loyalty counters on a Jace planeswalker token you control,
  creating one first if you control none. -/
  empowerJace : Option Nat := none
  /-- This permanent enters prepared (Reality Fracture). -/
  entersPrepared : Bool := false
  /-- Sorcery or instant copied while this permanent is prepared. -/
  prepareFace : Option AdventureFace := none
deriving Repr, Inhabited

namespace CardDef

def cantBeCountered (c : CardDef) : Bool :=
  c.castPermission == .cantBeCountered

def flashIfYouControlSubtype (c : CardDef) : Option String :=
  match c.castPermission with
  | .flashIfYouControl s => some s
  | _ => none

def castExiledWithSevenInGraveyard (c : CardDef) : Bool :=
  c.castPermission == .castExiledWithSevenInGraveyard

def castOnlyIfGraveyardAtLeast (c : CardDef) : Option Nat :=
  match c.castPermission with
  | .castOnlyIfGraveyardAtLeast n => some n
  | _ => none

def flashback (c : CardDef) : Option ManaCost :=
  match c.castOption with
  | .flashback cost _ => some cost
  | _ => none

def flashbackDiscard (c : CardDef) : Bool :=
  match c.castOption with
  | .flashback _ d => d
  | _ => false

def affinityForSubtype (c : CardDef) : Option String :=
  match c.castOption with
  | .affinity s => some s
  | _ => none

def giftTreasure (c : CardDef) : Bool :=
  c.castOption == .giftTreasure

def cascade (c : CardDef) : Nat :=
  match c.castOption with
  | .cascade n => n
  | _ => 0

def kicker (c : CardDef) : Option ManaCost :=
  match c.castOption with
  | .kicker cost => some cost
  | _ => none

def teamwork (c : CardDef) : Option Nat :=
  match c.castOption with
  | .teamwork n => some n
  | _ => none

def morph (c : CardDef) : Option ManaCost :=
  match c.castOption with
  | .morph cost => some cost
  | _ => none

def impending (c : CardDef) : Option (Nat × ManaCost) :=
  match c.castOption with
  | .impending n cost => some (n, cost)
  | _ => none

def ward (c : CardDef) : Option Nat :=
  match c.keywordRule with
  | .ward n => some n
  | _ => none

def anyNumberInDeck (c : CardDef) : Bool :=
  c.keywordRule == .anyNumberInDeck

def crew (c : CardDef) : Option Nat :=
  match c.keywordRule with
  | .crew n => some n
  | _ => none

def prowessInstances (c : CardDef) : Nat :=
  match c.keywordRule with
  | .prowess n => n
  | _ => 0

def daybound (c : CardDef) : Bool :=
  c.keywordRule == .daybound

def protectionFromColors (c : CardDef) : Array Color :=
  match c.keywordRule with
  | .protectionFromColors cols => cols
  | _ => #[]

def cycling (c : CardDef) : Option ManaCost :=
  match c.keywordRule with
  | .cycling cost => some cost
  | _ => none

def canBeCommander (c : CardDef) : Bool :=
  c.keywordRule == .canBeCommander

def toxic (c : CardDef) : Nat :=
  match c.keywordRule with
  | .toxic n _ => n
  | _ => 0

def cantBlock (c : CardDef) : Bool :=
  match c.keywordRule with
  | .cantBlock | .toxic _ true => true
  | _ => false

def entersTapped (c : CardDef) : Bool :=
  c.entersTappedRule == .always

def entersTappedUnlessLegendary (c : CardDef) : Bool :=
  c.entersTappedRule == .unlessLegendary

def entersTappedUnlessEquipment (c : CardDef) : Bool :=
  c.entersTappedRule == .unlessEquipment

def entersTappedUnlessPlaneswalker (c : CardDef) : Bool :=
  c.entersTappedRule == .unlessPlaneswalker

def entersTappedUnlessTwoOtherLands (c : CardDef) : Bool :=
  c.entersTappedRule == .unlessTwoOtherLands

def entersTappedUnlessPayLife (c : CardDef) : Option Nat :=
  match c.entersTappedRule with
  | .unlessPayLife n => some n
  | _ => none

def entersTappedUnlessAnySubtype (c : CardDef) : Array String :=
  match c.entersTappedRule with
  | .unlessAnySubtype ts => ts
  | _ => #[]

def entersTappedUnlessNBasics (c : CardDef) : Option Nat :=
  match c.entersTappedRule with
  | .unlessNBasics n => some n
  | _ => none

def entersTappedUnlessOppLands (c : CardDef) : Option Nat :=
  match c.entersTappedRule with
  | .unlessOppLands n => some n
  | _ => none

def entersWithHopePerCreature (c : CardDef) : Bool :=
  c.entersWithCounters == .hopePerCreature

def entersWithPlusOneCounters (c : CardDef) : Nat :=
  match c.entersWithCounters with
  | .plusOne n => n
  | _ => 0

def entersWithIndestructibleCounter (c : CardDef) : Bool :=
  c.entersWithCounters == .indestructible

def entersWithShield (c : CardDef) : Nat :=
  match c.entersWithCounters with
  | .shield n => n
  | _ => 0

def asEntersChooseCreatureType (c : CardDef) : Bool :=
  c.asEntersChoose == .creatureType

def asEntersChooseOddEven (c : CardDef) : Bool :=
  c.asEntersChoose == .oddEven

def asEntersChooseCardType (c : CardDef) : Bool :=
  c.asEntersChoose == .cardType

def asEntersChooseMarduOrJeskai (c : CardDef) : Bool :=
  c.asEntersChoose == .marduOrJeskai

def costReductionIfCreatureDied (c : CardDef) : Nat :=
  match c.spellCostReduction with
  | .ifCreatureDied n => n
  | _ => 0

def costReductionIfTargetDamaged (c : CardDef) : Nat :=
  match c.spellCostReduction with
  | .ifTargetDamaged n => n
  | _ => 0

def costReductionIfTargetTapped (c : CardDef) : Nat :=
  match c.spellCostReduction with
  | .ifTargetTapped n => n
  | _ => 0

def costReductionIfTargetAttackingNontoken (c : CardDef) : Nat :=
  match c.spellCostReduction with
  | .ifTargetAttackingNontoken n => n
  | _ => 0

def costReductionIfTargetAttacking (c : CardDef) : Nat :=
  match c.spellCostReduction with
  | .ifTargetAttacking n => n
  | _ => 0

def costReductionIfYouControl (c : CardDef) : Option (Nat × String) :=
  match c.spellCostReduction with
  | .ifYouControl n s => some (n, s)
  | _ => none

def costReductionIfGyCreaturesAtLeast (c : CardDef) : Option (Nat × Nat) :=
  match c.spellCostReduction with
  | .ifGyCreaturesAtLeast min n => some (min, n)
  | _ => none

def costReductionEqualFlyingPower (c : CardDef) : Bool :=
  c.spellCostReduction == .equalFlyingPower

def costReductionGreatestPower (c : CardDef) : Bool :=
  c.spellCostReduction == .greatestPower

def costReductionGreatestToughness (c : CardDef) : Bool :=
  c.spellCostReduction == .greatestToughness

def costReductionEqualOppArtifacts (c : CardDef) : Bool :=
  c.spellCostReduction == .equalOppArtifacts

def additionalCostSacrificeArtifactOrCreature (c : CardDef) : Bool :=
  match c.additionalCost with
  | .sacrificeArtifactOrCreature _ | .sacrificeCreatureOrPlaneswalkerOrPay _ => true
  | _ => false

def additionalCostSacrificeCreatureOrPlaneswalker (c : CardDef) : Bool :=
  match c.additionalCost with
  | .sacrificeCreatureOrPlaneswalkerOrPay _ => true
  | _ => false

def additionalCostOrPayGeneric (c : CardDef) : Option Nat :=
  match c.additionalCost with
  | .sacrificeArtifactOrCreature opt => opt
  | .sacrificeCreatureOrPlaneswalkerOrPay n => some n
  | _ => none

def additionalCostDiscardOrPayGeneric (c : CardDef) : Option Nat :=
  match c.additionalCost with
  | .discardOrPay n => some n
  | _ => none

def additionalCostSacrificeCreature (c : CardDef) : Bool :=
  c.additionalCost == .sacrificeCreature

def additionalCostBeholdOrPay (c : CardDef) : Option (String × Nat) :=
  match c.additionalCost with
  | .beholdOrPay q n => some (q, n)
  | _ => none

def tapAddManaForEach (c : CardDef) : Array TapAddForEach :=
  match c.tapManaAbility with
  | .forEach es => es
  | _ => #[]

def tapAddAnyColorEqualToPower (c : CardDef) : Bool :=
  c.tapManaAbility == .anyColorEqualToPower

def tapAddAnyColorForInstantOrSorcery (c : CardDef) : Bool :=
  c.tapManaAbility == .anyColorForInstantOrSorcery

def tapAddOneOf (c : CardDef) : Array ManaType :=
  match c.tapManaAbility with
  | .oneOf ts => ts
  | _ => #[]

def tapAddOneOfIfEnteredOrBasic (c : CardDef) : Array ManaType :=
  match c.tapManaAbility with
  | .oneOfIfEnteredOrBasic ts => ts
  | _ => #[]

def tapAddAnyColor (c : CardDef) : Bool :=
  c.tapManaAbility == .anyColor

def tapSacrificeAddAnyColor (c : CardDef) : Bool :=
  c.tapManaAbility == .sacrificeAnyColor

def tapAddChosenColorPerDifferentPower (c : CardDef) : Bool :=
  c.tapManaAbility == .chosenColorPerDifferentPower

def tapAddAnyColorForLegendary (c : CardDef) : Bool :=
  c.tapManaAbility == .anyColorForLegendary

def tapAddTwoAmong (c : CardDef) : Array ManaType :=
  match c.tapManaAbility with
  | .twoAmong ts => ts
  | _ => #[]

def tapAddAnyColorAmongLegendaries (c : CardDef) : Bool :=
  c.tapManaAbility == .anyColorAmongLegendaries

def tapAddRestricted (c : CardDef) : Option (Array ManaType × String) :=
  match c.tapManaAbility with
  | .restricted ts r => some (ts, r)
  | _ => none

def tapPayLifeAddOneOf (c : CardDef) : Option (Nat × Array ManaType) :=
  match c.tapManaAbility with
  | .payLifeOneOf n ts => some (n, ts)
  | _ => none

def tapAddCommanderIdentity (c : CardDef) : Bool :=
  match c.tapManaAbility with
  | .commanderIdentity _ => true
  | _ => false

def commanderIdentityScryCreature (c : CardDef) : Bool :=
  c.tapManaAbility == .commanderIdentity true

def tapAddColorlessPerSubtype (c : CardDef) : Option String :=
  match c.tapManaAbility with
  | .colorlessPerSubtype s => some s
  | _ => none

def tapAddTogether (c : CardDef) : Array ManaType :=
  match c.tapManaAbility with
  | .together ts => ts
  | _ => #[]

def tapAddOneOfDealsDamage (c : CardDef) : Option (Array ManaType × Nat) :=
  match c.tapManaAbility with
  | .oneOfDealsDamage ts n => some (ts, n)
  | _ => none

def tapAddOppCouldProduce (c : CardDef) : Bool :=
  c.tapManaAbility == .oppCouldProduce

def tapAddYouCouldProduce (c : CardDef) : Bool :=
  c.tapManaAbility == .youCouldProduce

def filterMana (c : CardDef) : Option (ManaCost × Array ManaType) :=
  match c.tapManaAbility with
  | .filter cost ts => some (cost, ts)
  | _ => none

def chooseOneOrBoth (c : CardDef) : Bool :=
  c.modalRule == .chooseOneOrBoth

def chooseTwoIfYouControlSubtype (c : CardDef) : Option String :=
  match c.modalRule with
  | .chooseTwoIfYouControl s => some s
  | _ => none

def chooseBothIfTeamwork (c : CardDef) : Bool :=
  c.modalRule == .chooseBothIfTeamwork

def mayLookAtTopAnytime (c : CardDef) : Bool :=
  match c.topOfLibraryRule with
  | .lookAnytime | .playLands | .castCreatures | .elvenChorus => true
  | _ => false

def mayCastCreaturesFromTop (c : CardDef) : Bool :=
  match c.topOfLibraryRule with
  | .castCreatures | .elvenChorus => true
  | _ => false

def mayPlayLandsFromTop (c : CardDef) : Bool :=
  c.topOfLibraryRule == .playLands

def grantCreaturesTapAddAnyColor (c : CardDef) : Bool :=
  match c.topOfLibraryRule with
  | .elvenChorus | .grantCreaturesTapAnyColor => true
  | _ => false

def foodAlsoCreatesTreasure (c : CardDef) : Bool :=
  c.staticRule == .foodAlsoCreatesTreasure

def othersEnterWithPlusOneEqualToughness (c : CardDef) : Bool :=
  c.staticRule == .othersEnterWithPlusOneEqualToughness

def powerPerMountain (c : CardDef) : Nat :=
  match c.staticRule with
  | .powerPerMountain n => n
  | _ => 0

def extraLandIfOtherSubtype (c : CardDef) : Option String :=
  match c.staticRule with
  | .extraLandIfOtherSubtype s => some s
  | _ => none

def tokenDoubling (c : CardDef) : Bool :=
  match c.staticRule with
  | .tokenDoubling _ => true
  | _ => false

def drawTwoExceptFirstDrawStep (c : CardDef) : Bool :=
  match c.staticRule with
  | .drawTwoExceptFirstDrawStep | .tokenDoubling true => true
  | _ => false

def exileOppCreaturesInstead (c : CardDef) : Bool :=
  c.staticRule == .exileOppCreaturesInstead

def firstCreatureCostsLess (c : CardDef) : Nat :=
  match c.staticRule with
  | .firstCreatureDiscount n _ => n
  | _ => 0

def firstCreatureHasFlash (c : CardDef) : Bool :=
  match c.staticRule with
  | .firstCreatureDiscount _ b => b
  | _ => false

def hexproofIndestructibleIfLore (c : CardDef) : Option Nat :=
  match c.staticRule with
  | .hexproofIndestructibleIfLore n => some n
  | _ => none

def costReductionNotFromHand (c : CardDef) : Nat :=
  match c.staticRule with
  | .costReductionNotFromHand n => n
  | _ => 0

def grantLandsTapAnyColor (c : CardDef) : Bool :=
  c.staticRule == .grantLandsTapAnyColor

def freeCastIfControlCommander (c : CardDef) : Bool :=
  c.staticRule == .freeCastIfControlCommander

def opponentsCantGainLife (c : CardDef) : Bool :=
  c.staticRule == .opponentsCantGainLife

def cantLoseGame (c : CardDef) : Bool :=
  match c.staticRule with
  | .cantLoseAndOpponentsCantWin _ => true
  | _ => false

def opponentsCantWin (c : CardDef) : Bool :=
  match c.staticRule with
  | .cantLoseAndOpponentsCantWin _ => true
  | _ => false

def creaturesCantGetMinusCounters (c : CardDef) : Bool :=
  match c.staticRule with
  | .creaturesCantGetMinusCounters | .cantLoseAndOpponentsCantWin true => true
  | _ => false

def powerPerUnspentMana (c : CardDef) : Bool :=
  match c.staticRule with
  | .powerPerUnspentMana _ => true
  | _ => false

def unspentManaBecomesColorless (c : CardDef) : Bool :=
  match c.staticRule with
  | .unspentManaBecomesColorless | .powerPerUnspentMana true => true
  | _ => false

def eminenceSphinxReduction (c : CardDef) : Nat :=
  match c.staticRule with
  | .eminenceSphinxReduction n => n
  | _ => 0

def protectionFromChosenCardType (c : CardDef) : Bool :=
  c.staticRule == .protectionFromChosenCardType

def corruptedToxicLifelink (c : CardDef) : Bool :=
  c.staticRule == .corruptedToxicLifelink

def grantTeamPlusTwoFlying (c : CardDef) : Bool :=
  c.staticRule == .grantTeamPlusTwoFlying

/-- Color from color indicator, otherwise from mana cost (CR 202.2). -/
def colors (c : CardDef) : ColorSet :=
  match c.colorIndicator with
  | some cs => cs
  | none => c.manaCost.colors

/-- Commander color identity of this face: mana cost, color indicator, and
basic land types (CR 903.4). Does not look at the other face. -/
def faceColorIdentity (c : CardDef) : ColorSet :=
  let fromCost :=
    match c.colorIndicator with
    | some cs => c.manaCost.colors.union cs
    | none => c.manaCost.colors
  c.subtypes.foldl (fun acc s =>
    match manaForBasicLandType s with
    | some col => acc.insert col
    | none => acc) fromCost

/-- Combined color identity of both faces of a DFC (CR 903.4 / MSH 18). -/
def colorIdentity (c : CardDef) : ColorSet :=
  match c.otherFace with
  | none => c.faceColorIdentity
  | some back => c.faceColorIdentity.union back.faceColorIdentity

/-- True when `t` is among this card's types. -/
def hasType (c : CardDef) (t : CardType) : Bool := c.types.any (· == t)

/-- True when `s` is among this card's subtypes. -/
def hasSubtype (c : CardDef) (s : Subtype) : Bool := c.subtypes.any (· == s)

/-- True when `s` is among this card's supertypes. -/
def hasSupertype (c : CardDef) (s : Supertype) : Bool := c.supertypes.any (· == s)

def isLand (c : CardDef) : Bool := c.hasType .land
def isCreature (c : CardDef) : Bool := c.hasType .creature
def isArtifact (c : CardDef) : Bool := c.hasType .artifact
def isInstant (c : CardDef) : Bool := c.hasType .instant
def isSorcery (c : CardDef) : Bool := c.hasType .sorcery
def isInstantOrSorcery (c : CardDef) : Bool := c.types.any CardType.isInstantOrSorcery
def isEnchantment (c : CardDef) : Bool := c.hasType .enchantment
def isPlaneswalker (c : CardDef) : Bool := c.hasType .planeswalker
def isBattle (c : CardDef) : Bool := c.hasType .battle
def isVanguard (c : CardDef) : Bool := c.hasType .vanguard
def isPermanentCard (c : CardDef) : Bool := c.types.any CardType.isPermanentType
/-- Aura subtype on an Enchantment (CR 303.4). -/
def isAura (c : CardDef) : Bool :=
  c.isEnchantment && c.hasSubtype "Aura"
/-- Equipment subtype on an Artifact (CR 301.5). -/
def isEquipment (c : CardDef) : Bool :=
  c.isArtifact && c.hasSubtype "Equipment"

/-- Names a player may choose for “choose a card name”, including an
Adventure face (Gatherer ruling on adventurer cards). -/
def choosableNames (c : CardDef) : Array String :=
  match c.adventure with
  | some adv => #[c.name, adv.name]
  | none => #[c.name]

/-- Timing of a sorcery: also the default for permanent spells without flash (CR 302.1, 307.1). -/
def hasSorcerySpeed (c : CardDef) : Bool :=
  !c.isInstant && !c.isLand && !c.keywords.flash

def hasInstantSpeed (c : CardDef) : Bool :=
  c.isInstant || c.keywords.flash

/-- Modal spell with “Choose one” (CR 700.2). -/
def isModal (c : CardDef) : Bool :=
  !c.spellModes.isEmpty

/-- Modes of a modal spell; empty when the card is not modal. -/
def modes (c : CardDef) : Array Effect :=
  c.spellModes

/-- Whether casting this card requires choosing a target (CR 115.1, 303.4). -/
def requiresTarget (c : CardDef) : Bool :=
  c.isAura ||
  match c.spellEffect with
  | some e => e.requiresTarget
  | none => !c.spellModes.isEmpty && c.spellModes.all (·.requiresTarget)

/-- True when the printed spell may be announced with zero targets. -/
def allowsZeroTargets (c : CardDef) : Bool :=
  match c.spellEffect with
  | some e => e.allowsZeroTargets
  | none => false

/-- True when the printed effect or a mode is classified as `k`. -/
def hasCastKind (c : CardDef) (k : SpellCastKind) : Bool :=
  c.spellEffect.any (fun e => e.castKind == k)

/-- True when a modal mode is classified as `k`. -/
def hasModeCastKind (c : CardDef) (k : SpellCastKind) : Bool :=
  c.spellModes.any (fun e => e.castKind == k)

/-- True when this card has an Adventure (CR 715). -/
def hasAdventure (c : CardDef) : Bool :=
  c.adventure.isSome

def manaValue (c : CardDef) : Nat := c.manaCost.manaValue

/-- Basic land types on this card produce the corresponding mana (CR 305.6). -/
def basicLandMana (c : CardDef) : Array Color :=
  c.subtypes.filterMap manaForBasicLandType

/-- `{T}: Add {M}` abilities that produce one mana, from basic land types or
an explicit `tapAddMana` list. -/
def simpleTapAddMana (c : CardDef) : Array ManaType :=
  c.basicLandMana.map ManaType.colored ++ c.tapAddMana

/-- `{T}: Add` types from modeled activated mana abilities. -/
def mshTapAddMana (c : CardDef) : Array ManaType :=
  c.activatedAbilities.foldl (fun acc ab =>
    match ab.effect.resolution with
    | .addMana types (.fixed 1) .none | .addMana types (.fixed 1) .cantNonartifact => acc ++ types
    | _ => acc) #[]

/-- `{T}: Add` types gated on this land entering this turn or a basic land. -/
def enteredOrBasicAddMana (c : CardDef) : Array ManaType :=
  c.tapAddOneOfIfEnteredOrBasic ++ c.mshTapAddMana

/-- True when a `{T}: Add` ability requires this land entered this turn or
a basic land you control. -/
def requiresEnteredOrBasicAdd (c : CardDef) : Bool :=
  !c.tapAddOneOfIfEnteredOrBasic.isEmpty

/-- True when an activated ability adds any color of mana. -/
def hasAnyColorActivatedAdd (c : CardDef) : Bool :=
  c.activatedAbilities.any (fun ab =>
    match ab.effect.resolution with
    | .addMana #[] _ note => note != .none
    | _ => false)

/-- All `{T}: Add` mana types this card can produce. -/
def manaAbilities (c : CardDef) : Array ManaType :=
  c.simpleTapAddMana ++ c.tapAddOneOf ++ c.tapAddManaForEach.map (·.mana) ++
    c.enteredOrBasicAddMana ++
    (if c.tapAddAnyColorEqualToPower || c.tapAddAnyColorForInstantOrSorcery ||
        c.tapAddAnyColor || c.tapSacrificeAddAnyColor ||
        c.tapAddAnyColorForLegendary || c.tapAddTwoAmong.size >= 2 ||
        c.tapAddAnyColorAmongLegendaries || c.tapAddCommanderIdentity ||
        c.hasAnyColorActivatedAdd || c.tapAddChosenColorPerDifferentPower then
      (Color.all.map ManaType.colored).toArray
     else #[])

/-- Lowercase ASCII for comparing Oracle keyword lines to `Keywords.toList`. -/
def lowerAscii (s : String) : String :=
  s.map Char.toLower

/-- Drop a trailing Oracle reminder parenthetical, e.g. `Menace (This creature...)`. -/
def stripReminderParenthetical (s : String) : String :=
  match s.splitOn "(" with
  | [] => s
  | head :: _ => head.trimAscii.copy

/-- True when `line` restates modeled keywords, e.g. `Haste` or `Reach, deathtouch`.
A line that is only a parenthetical (e.g. basic-land `{T}: Add` reminder text)
is not a keyword restatement. -/
def isKeywordRestatement (k : Keywords) (line : String) : Bool :=
  let kw := k.toList
  let cleaned := stripReminderParenthetical ((line.replace "." "").trimAscii.copy)
  if cleaned.isEmpty then false
  else
    let parts := cleaned.splitOn "," |>.map (fun s => s.trimAscii.copy) |>.filter (fun s => !s.isEmpty)
    !parts.isEmpty && parts.all (fun p => kw.any (fun w => w == lowerAscii p))

/-- Gatherer delimiter between an adventurer card's primary and Adventure faces. -/
def isAdventureDelimiter (line : String) : Bool :=
  line == "//ADV//" || line.startsWith "//ADV//"

/-- Drop a leading `//ADV//` marker. The remainder (Adventure name and mana
cost) is kept so leftover Oracle text does not lose printed mana symbols. -/
def stripAdventureDelimiter (line : String) : Option String :=
  if line == "//ADV//" then none
  else if line.startsWith "//ADV//" then
    let rest := (line.drop "//ADV//".length).trimAscii.copy
    if rest.isEmpty then none else some rest
  else some line

/-- `{T}: Add {C}` lines from an explicit `tapAddMana` list. Basic land types
print the parenthetical reminder instead. -/
def explicitTapAddLines (c : CardDef) : List String :=
  c.tapAddMana.toList.map (fun t => s!"\{T}: Add \{{t.letter}}")

/-- `({T}: Add {R}.)` for each basic land type, when no other tap-add list is set. -/
def basicLandReminderLines (c : CardDef) : List String :=
  if !c.tapAddMana.isEmpty then []
  else c.basicLandMana.toList.map fun col => s!"(\{T}: Add \{{col.letter}}.)"

/-- Adventure name, cost, and spell, without the Gatherer `//ADV//` marker. -/
def adventureLines (c : CardDef) : List String :=
  match c.adventure with
  | none => []
  | some a =>
    let header :=
      if a.manaCost.symbols.isEmpty then a.name else s!"{a.name} {a.manaCost}"
    let extra :=
      (if a.additionalCostSacrificeCreature then
        ["As an additional cost to cast this spell, sacrifice a creature."]
       else []) ++
      match a.spellEffect with
      | some e => [e.phrase]
      | none => []
    header :: extra ++ a.extraLines.toList

/-- Prepare-spell name, cost, and effect. -/
def prepareLines (c : CardDef) : List String :=
  match c.prepareFace with
  | none =>
    if c.entersPrepared then ["This creature enters prepared."] else []
  | some a =>
    let header :=
      if a.manaCost.symbols.isEmpty then a.name else s!"{a.name} {a.manaCost}"
    let effect :=
      match a.spellEffect with
      | some e => [e.phrase]
      | none => []
    (if c.entersPrepared then ["This creature enters prepared."] else []) ++
      [header] ++ effect ++ a.extraLines.toList

/-- Empower Jace printed on this spell. -/
def empowerLines (c : CardDef) : List String :=
  match c.empowerJace with
  | some n => [s!"Empower Jace {n}."]
  | none => []

/-- `{T}: Add {U} or {B}.` -/
def tapAddOneOfLines (c : CardDef) : List String :=
  if c.tapAddOneOf.isEmpty then []
  else [s!"\{T}: Add {manaSymbolsText c.tapAddOneOf " or "}."]

/-- `{T}: Add {U} or {B}` gated on entering this turn or a basic land. -/
def tapAddOneOfIfEnteredLines (c : CardDef) : List String :=
  if c.tapAddOneOfIfEnteredOrBasic.isEmpty then []
  else
    [s!"\{T}: Add {manaSymbolsText c.tapAddOneOfIfEnteredOrBasic " or "}. Activate only if this land entered this turn or if you control a basic land."]

/-- `{T}: Add` for each permanent of a listed type. -/
def tapAddForEachLines (c : CardDef) : List String :=
  c.tapAddManaForEach.toList.map TapAddForEach.toNotation

/-- Elf-restricted `{T}: Add` X mana of any color equal to power. -/
def tapAddAnyColorEqualToPowerLine (c : CardDef) : List String :=
  if c.tapAddAnyColorEqualToPower then
    ["{T}: Add X mana of any one color, where X is this creature's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources."]
  else []

/-- Instant/sorcery-restricted `{T}: Add` one mana of any color. -/
def tapAddAnyColorForInstantOrSorceryLine (c : CardDef) : List String :=
  if c.tapAddAnyColorForInstantOrSorcery then
    ["{T}: Add one mana of any color. Spend this mana only to cast an instant or sorcery spell."]
  else []

/-- True when CR 601.2b must announce a sacrifice-or-pay or discard-or-pay
additional cost. -/
def announcesAdditionalCost (c : CardDef) : Bool :=
  c.additionalCostOrPayGeneric.isSome || c.additionalCostDiscardOrPayGeneric.isSome ||
    c.additionalCostBeholdOrPay.isSome

/-- Additional cost that sacrifices an artifact or creature (optionally or pay `{n}`). -/
def additionalCostSacrificeArtifactOrCreatureLine (c : CardDef) : List String :=
  if c.additionalCostSacrificeArtifactOrCreature then
    match c.additionalCostOrPayGeneric with
    | some n =>
      [s!"As an additional cost to cast this spell, sacrifice an artifact or creature or pay \{{n}}"]
    | none =>
      ["As an additional cost to cast this spell, sacrifice an artifact or creature"]
  else
    match c.additionalCostDiscardOrPayGeneric with
    | some n =>
      [s!"As an additional cost to cast this spell, discard a card or pay \{{n}}."]
    | none =>
      match c.additionalCostBeholdOrPay with
      | some (quality, n) =>
        [s!"As an additional cost to cast this spell, behold a {quality} or pay \{{n}}."]
      | none => []

/-- `{T}cycling` and other typecycling, printed as `Mountaincycling {1}`. -/
def activatedNotation (ab : ActivatedAbility) : String :=
  if ab.activateFromHand && ab.cost.discardSource then
    match ab.effect.resolution with
    | .searchLibrary (.returnToHand (.landSubtype t) _) =>
      if t == "Plan" then ab.toNotation else s!"{t}cycling {ab.cost.mana}"
    | _ => ab.toNotation
  else
    ab.toNotation

/-- Spell effect, or `Choose one —` when the spell is modal. -/
def spellLines (c : CardDef) : List String :=
  if !c.spellModes.isEmpty then
    [s!"Choose one — {String.intercalate "; " (c.spellModes.toList.map Effect.toNotation)}"]
  else
    match c.spellEffect with
    | some e => [Effect.toNotation e]
    | none => []

/-- `{T}: Add` mana abilities, additional costs, activated, static, triggered, and spell abilities. -/
def structuredAbilityLines (c : CardDef) : List String :=
  c.explicitTapAddLines ++
  c.basicLandReminderLines ++
  c.tapAddOneOfLines ++
  c.tapAddOneOfIfEnteredLines ++
  c.tapAddForEachLines ++
  c.tapAddAnyColorEqualToPowerLine ++
  c.tapAddAnyColorForInstantOrSorceryLine ++
  c.additionalCostSacrificeArtifactOrCreatureLine ++
  c.activatedAbilities.toList.map activatedNotation ++
  c.staticAbilities.toList.map StaticAbility.toNotation ++
  c.triggeredAbilities.toList.map TriggeredAbility.toNotation ++
  c.adventureLines ++
  c.prepareLines ++
  c.empowerLines ++
  c.spellLines

/-- Modeled ability lines. Keyword-only lines are omitted; those print with
`Keywords`. -/
def leftoverOracleLines (c : CardDef) : List String :=
  c.structuredAbilityLines.filter fun line => !isKeywordRestatement c.keywords line

/-- Abilities to print in the demo, taken from the modeled fields. -/
def abilitiesText (c : CardDef) : String :=
  String.intercalate "; " (structuredAbilityLines c)

/-- Keywords `k` plus leftover Oracle / structured abilities. -/
def keywordsAndAbilitiesOf (c : CardDef) (k : Keywords) : String :=
  String.intercalate " "
    ([toString k, c.abilitiesText].filter (fun s => !s.isEmpty))

/-- Keywords and abilities shown next to a card in the demo. -/
def keywordsAndAbilities (c : CardDef) : String :=
  c.keywordsAndAbilitiesOf c.keywords

def typeLine (c : CardDef) : String :=
  formatTypeLine c.supertypes c.types c.subtypes

/-- One side of a power/toughness box (CR 208.1 / 208.2).
A star plus constant `k` prints as `k+*` (CR 208.2a writes `1+*`). A bare
star, and `*+0`, print as `*`. -/
def renderPrintedStat (n : Option Int) (star : Bool) : String :=
  if star then
    match n with
    | some k => if k == 0 then "*" else s!"{k}+*"
    | none => "*"
  else
    match n with
    | some k => toString k
    | none => "*"

/-- Printed `power/toughness`, if this object has one.
A creature with neither a number nor a star prints `*/*`. Any other object
with neither prints nothing (CR 208.3). -/
def formatPowerToughness (power toughness : Option Int)
    (powerStar toughnessStar isCreature : Bool) : Option String :=
  if power.isNone && toughness.isNone && !powerStar && !toughnessStar then
    if isCreature then some "*/*" else none
  else
    some s!"{renderPrintedStat power powerStar}/{renderPrintedStat toughness toughnessStar}"

def ptString (c : CardDef) : String :=
  (formatPowerToughness c.power c.toughness c.powerStar c.toughnessStar c.isCreature).getD ""

/-- Name, printed mana cost if any, type line, P/T, then keywords and abilities.
Cards with no mana cost (lands, and other objects whose cost cannot be paid)
omit the cost rather than printing `{0}` (CR 202.1b / 118.6). -/
def summary (c : CardDef) : String :=
  String.intercalate " "
    ([c.name, toString c.manaCost, c.typeLine, c.ptString, c.keywordsAndAbilities].filter
      (fun s => !s.isEmpty))

instance : ToString CardDef where
  toString := summary

/-- True when this card itself has improvise (MSH). -/
def hasImprovise (c : CardDef) : Bool :=
  c.staticAbilities.any (fun
    | .improvise => true
    | _ => false)

/-- True when this permanent grants improvise to noncreature spells you cast. -/
def grantsImproviseToNoncreature (c : CardDef) : Bool :=
  c.staticAbilities.any (fun
    | .noncreatureSpellsHaveImprovise => true
    | _ => false)

/-- True when this permanent has a boast ability (MSH). -/
def hasBoast (c : CardDef) : Bool :=
  c.staticAbilities.any (fun
    | .boast => true
    | _ => false)

/-- Sneak alternative cost, if any (MSH). -/
def sneakCost (c : CardDef) : Option ManaCost :=
  c.staticAbilities.foldl (fun acc ab =>
    match acc, ab with
    | none, .sneak cost => some cost
    | acc, _ => acc) none

/-- Equip worthy: legendary non-Villain creature that's red or white. -/
def isWorthy (c : CardDef) : Bool :=
  c.hasSupertype .legendary &&
    !c.hasSubtype "Villain" &&
    (c.colors.contains .red || c.colors.contains .white)

/-- Equip worthy keyword on this Equipment (MSH). -/
def hasEquipWorthy (c : CardDef) : Bool :=
  c.activatedAbilities.any (·.equipWorthy)

/-- Spell, modal, adventure, prepare, and Saga-chapter effects on this face. -/
def spellLikeEffects (c : CardDef) : Array Effect :=
  let modes := if c.spellModes.isEmpty then
      match c.spellEffect with
      | some e => #[e]
      | none => #[]
    else c.spellModes
  let adv := match c.adventure with
    | some a => match a.spellEffect with
      | some e => #[e]
      | none => #[]
    | none => #[]
  let prep := match c.prepareFace with
    | some a => match a.spellEffect with
      | some e => #[e]
      | none => #[]
    | none => #[]
  let chapters := match c.saga with
    | some s => s.chapters.filterMap (·.chapterEffect)
    | none => #[]
  modes ++ adv ++ prep ++ chapters

/-- Why this face is not fully parsed or its effects are not fully modelled.
Does not look at `otherFace`. -/
def faceModellingError? (c : CardDef) : Option String :=
  let unparsed : Option String :=
    c.staticAbilities.foldl (fun acc ab =>
      match acc, ab with
      | some e, _ => some e
      | none, .printed line => some s!"unparsed rules line on {c.name}: {line}"
      | none, _ => none) none
      <|> (c.adventure.bind fun a =>
        a.extraLines[0]?.map fun line => s!"unparsed rules line on {a.name}: {line}")
      <|> (c.prepareFace.bind fun a =>
        a.extraLines[0]?.map fun line => s!"unparsed rules line on {a.name}: {line}")
  let spell : Option String :=
    c.spellLikeEffects.foldl (fun acc e =>
      match acc with
      | some err => some err
      | none =>
        if e.resolution.doesNothingAsSpell then
          some s!"{c.name} is not fully modelled: {e.toNotation}"
        else none) none
  let activated : Option String :=
    c.activatedAbilities.foldl (fun acc ab =>
      match acc with
      | some err => some err
      | none =>
        if ab.effect.resolution.doesNothingAsActivated then
          some s!"{c.name} activated ability is not fully modelled: {ab.effect.toNotation}"
        else none) none
  unparsed <|> spell <|> activated

/-- Why `c` or its back face is not fully parsed or fully modelled.
`none` when every rules line was recognized and every spell, mode,
adventure, prepare face, Saga chapter, and activated ability resolves. -/
def modellingError? (c : CardDef) : Option String :=
  c.faceModellingError? <|> (c.otherFace.bind faceModellingError?)

end CardDef

namespace AdventureFace

/-- Characteristics used while this card is on the stack as an Adventure (CR 715.3b). -/
def toCardDef (a : AdventureFace) : CardDef := {
  name := a.name
  manaCost := a.manaCost
  types := a.types
  subtypes := a.subtypes
  spellEffect := a.spellEffect
  staticAbilities := a.extraLines.map StaticAbility.printed
  empowerJace := a.empowerJace
  additionalCost := if a.additionalCostSacrificeCreature then .sacrificeCreature else .none
}

/-- True when this Adventure's effect is classified as `k`. -/
def hasCastKind (a : AdventureFace) (k : SpellCastKind) : Bool :=
  a.spellEffect.any (fun e => e.castKind == k)

end AdventureFace

/-- Constructed-play four-of rule applies to non-basic-land English names (CR 100.2a). -/
def isBasicLandCard (c : CardDef) : Bool :=
  c.isLand && c.hasSupertype .basic

/-- A land card with the given land type (CR 205.3i / 305.7). -/
def isLandTypeCard (c : CardDef) (landType : String) : Bool :=
  c.isLand && c.hasSubtype landType

/-- A card with the Forest land type (CR 205.3i / 305.7). -/
def isForestCard (c : CardDef) : Bool :=
  isLandTypeCard c "Forest"

end Mtg.Engine
