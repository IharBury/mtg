import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.Targeting
import Mtg.Engine.Card.Text
import Mtg.Engine.Card.Token
import Mtg.Engine.Mana
import Mtg.Engine.TypeLine

/-!
# Resolutions (CR 608 / 603)

One vocabulary for spells, triggered abilities, and activated abilities.
`Resolution` is that inductive. `SpellResolution` and
`TriggeredAbility.TriggerResolution` are abbreviations for it.
-/

namespace Mtg.Engine

/-- How the demonstration agent classifies a spell when choosing what to cast.
Adding a constructor is a compile error in `SpellResolution.toPhrase` rather than
silently skipping the new effect. -/
inductive SpellCastKind where
  /-- Spell classification for agent heuristics: damage/fight (`false, false`), destroy/counter (`true, false`), pump (`false, true`), or utility (`true, true`). -/
  | spellCastKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (cat1 : Bool := false) (cat2 : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace SpellCastKind

@[match_pattern] abbrev damageOrFight (creatureOnly : Bool := false) (fight : Bool := false) : SpellCastKind :=
  .spellCastKind creatureOnly fight false false false
@[match_pattern] abbrev destroyOrCounter (flying : Bool := false) (artifactOrLand : Bool := false) (counterSpell : Bool := false) : SpellCastKind :=
  .spellCastKind flying artifactOrLand counterSpell true false
@[match_pattern] abbrev pumpSpell (mass : Bool := false) : SpellCastKind :=
  .spellCastKind mass false false false true
@[match_pattern] abbrev utilitySpell (draw : Bool := false) : SpellCastKind :=
  .spellCastKind draw false false true true
@[match_pattern] abbrev burn : SpellCastKind := .damageOrFight false false
@[match_pattern] abbrev creatureDamage : SpellCastKind := .damageOrFight true false
@[match_pattern] abbrev fight : SpellCastKind := .damageOrFight false true
@[match_pattern] abbrev destroyCreature : SpellCastKind := .destroyOrCounter false false false
@[match_pattern] abbrev destroyFlying : SpellCastKind := .destroyOrCounter true false false
@[match_pattern] abbrev destroyArtifactOrLand : SpellCastKind := .destroyOrCounter false true false
@[match_pattern] abbrev counter : SpellCastKind := .destroyOrCounter false false true
@[match_pattern] abbrev pump : SpellCastKind := .pumpSpell false
@[match_pattern] abbrev massPump : SpellCastKind := .pumpSpell true
@[match_pattern] abbrev extraLand : SpellCastKind := .utilitySpell false
@[match_pattern] abbrev draw : SpellCastKind := .utilitySpell true

end SpellCastKind

/-- How the demonstration agent classifies an activated-ability mode. -/
inductive AbilityCastKind where
  /-- Activated ability classification: creature damage (`false, false`), destroy colorless (`true, false`), or other (`false, true`). -/
  | abilityCastKind (destroyColorless : Bool := false) (other : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace AbilityCastKind

@[match_pattern] abbrev creatureDamage : AbilityCastKind := .abilityCastKind false false
@[match_pattern] abbrev destroyColorless : AbilityCastKind := .abilityCastKind true false
@[match_pattern] abbrev other : AbilityCastKind := .abilityCastKind false true
@[match_pattern] abbrev sacrificeSourceKind (controllerSacrifices : Bool := false) (movedAsSacrificed : Bool := false) : AbilityCastKind :=
  .abilityCastKind controllerSacrifices movedAsSacrificed
@[match_pattern] abbrev isSacrificed : AbilityCastKind := .sacrificeSourceKind false false
@[match_pattern] abbrev controllerSacrifices : AbilityCastKind := .sacrificeSourceKind true false
@[match_pattern] abbrev movedAsSacrificed : AbilityCastKind := .sacrificeSourceKind false true
@[match_pattern] abbrev returnNoteKind (returnedPermanent : Bool := false) (delayedBirds : Bool := false) : AbilityCastKind :=
  .abilityCastKind returnedPermanent delayedBirds
@[match_pattern] abbrev none : AbilityCastKind := .returnNoteKind false false
@[match_pattern] abbrev returnedPermanent : AbilityCastKind := .returnNoteKind true false
@[match_pattern] abbrev delayedBirds : AbilityCastKind := .returnNoteKind false true
@[match_pattern] abbrev surveilRecord (armReturn : Bool := false) (returnCardOrEye : Bool := false) : AbilityCastKind :=
  .abilityCastKind armReturn returnCardOrEye
@[match_pattern] abbrev armReturnLifeGained : AbilityCastKind := .surveilRecord true false
@[match_pattern] abbrev returnNoncreatureNonland : AbilityCastKind := .surveilRecord false true
@[match_pattern] abbrev eyeOfJace : AbilityCastKind := .surveilRecord true true

end AbilityCastKind

/-- Which milled cards `SpellResolution.millThenPut` puts into hand. -/
inductive MilledToHand where
  /-- Up to one (`all = false`), every (`all = true`), or up to `max` (`max = some max`) milled card(s) of type `a` or `b`. -/
  | milledPickKind (a : CardType := .creature) (b : CardType := .land) (all : Bool := false)
      (max : Option Nat := none)
deriving Repr, Inhabited, BEq, DecidableEq

namespace MilledToHand

@[match_pattern] abbrev twoTypes (a b : CardType) (all : Bool := false) : MilledToHand :=
  .milledPickKind a b all none
@[match_pattern] abbrev upTo (max : Nat) (ty : CardType) : MilledToHand :=
  .milledPickKind ty .creature false (some max)
@[match_pattern] abbrev oneOf (a b : CardType) : MilledToHand := .twoTypes a b false
@[match_pattern] abbrev allOf (a b : CardType) : MilledToHand := .twoTypes a b true

end MilledToHand

/-- Which spells `SpellResolution.spellsCostLessThisTurn` makes cheaper. -/
inductive SpellCostLess where
  /-- Spells of card type `ty` (`s = none`, CR 205.2a) or supertype `s` (`s = some s`, CR 205.4a). -/
  | spellCostLessKind (ty : CardType := .creature) (s : Option Supertype := none)
deriving Repr, Inhabited, BEq, DecidableEq

namespace SpellCostLess

@[match_pattern] abbrev cardType (ty : CardType) : SpellCostLess := .spellCostLessKind ty none
@[match_pattern] abbrev supertype (s : Supertype) : SpellCostLess := .spellCostLessKind .creature (some s)

end SpellCostLess

/-- Which permanents `SharedTrigger.plusOneEachYouControl` puts a counter on. -/
inductive YouControlPlusOne where
  /-- Each creature you control (`subtype = none`, or two counters with the city's blessing when `citysBlessing = true`) or each permanent of `subtype` you control (`subtype = some subtype`). -/
  | plusOneGroupKind (citysBlessing : Bool := false) (subtype : Option String := none)
deriving Repr, Inhabited, BEq

namespace YouControlPlusOne

@[match_pattern] abbrev creaturesYouControl (citysBlessing : Bool := false) : YouControlPlusOne :=
  .plusOneGroupKind citysBlessing none
@[match_pattern] abbrev subtype (subtype : String) : YouControlPlusOne :=
  .plusOneGroupKind false (some subtype)
@[match_pattern] abbrev eachCreature : YouControlPlusOne := .creaturesYouControl false
@[match_pattern] abbrev citysBlessing : YouControlPlusOne := .creaturesYouControl true

end YouControlPlusOne

namespace TriggeredAbility

/-- Spending restriction or color choice for `Resolution.addMana` (CR 106.4). -/
inductive ManaSpendNote where
  /-- Spend scope (`false, false`), chosen color (`true, false`), spell type restriction (`false, true`), or subtype spend restriction (`subtype = some s`). -/
  | manaSpendNoteKind (alt1 : Bool := false) (alt2 : Bool := false)
      (chosenColor : Bool := false) (spellType : Bool := false)
      (subtype : Option String := Option.none)
deriving Repr, Inhabited, BEq, DecidableEq

namespace ManaSpendNote

@[match_pattern] abbrev spendOrColorNote (alt1 : Bool := false) (alt2 : Bool := false)
    (chosenColor : Bool := false) (spellType : Bool := false) : ManaSpendNote :=
  .manaSpendNoteKind alt1 alt2 chosenColor spellType Option.none
@[match_pattern] abbrev subtypeSpend (subtype : String) (orAbilities : Bool := false) : ManaSpendNote :=
  .manaSpendNoteKind orAbilities false false false (some subtype)
@[match_pattern] abbrev spendScope (creatureSources : Bool := false) (equipment : Bool := false) : ManaSpendNote :=
  .spendOrColorNote creatureSources equipment false false
@[match_pattern] abbrev chosenColor (combination : Bool := false) : ManaSpendNote :=
  .spendOrColorNote combination false true false
@[match_pattern] abbrev spellTypeRestriction (noncreature : Bool := false) (cantNonartifact : Bool := false) : ManaSpendNote :=
  .spendOrColorNote noncreature cantNonartifact false true
@[match_pattern] abbrev none : ManaSpendNote := .spendScope false false
@[match_pattern] abbrev creatureSources : ManaSpendNote := .spendScope true false
@[match_pattern] abbrev equipment : ManaSpendNote := .spendScope false true
@[match_pattern] abbrev anyColor : ManaSpendNote := .chosenColor false
@[match_pattern] abbrev anyCombination : ManaSpendNote := .chosenColor true
@[match_pattern] abbrev subtypeSpells (subtype : String) : ManaSpendNote := .subtypeSpend subtype false
@[match_pattern] abbrev subtypeSpellsOrAbilities (subtype : String) : ManaSpendNote := .subtypeSpend subtype true
@[match_pattern] abbrev artifactSpell : ManaSpendNote := .spellTypeRestriction false false
@[match_pattern] abbrev noncreatureSpell : ManaSpendNote := .spellTypeRestriction true false
@[match_pattern] abbrev cantNonartifact : ManaSpendNote := .spellTypeRestriction false true

end ManaSpendNote

/-- How `TriggerResolution.sacrifice` moves the source when `what` is
`.source` or `.sacrificedSource`. -/
abbrev SacrificeSourceHow := AbilityCastKind

namespace SacrificeSourceHow

@[match_pattern] abbrev isSacrificed : SacrificeSourceHow := .sacrificeSourceKind false false
@[match_pattern] abbrev controllerSacrifices : SacrificeSourceHow := .sacrificeSourceKind true false
@[match_pattern] abbrev movedAsSacrificed : SacrificeSourceHow := .sacrificeSourceKind false true

end SacrificeSourceHow

/-- Which MSH reflexive `TriggerResolution.queueReflexive` queues.
`toNat` is the index `Resolution.mshReflexive` matches. -/
inductive TriggerReflexiveKind where
  /-- Combat/control (`false, false`), zone/damage (`true, false`), or target/return (`false, true`) reflexive. -/
  | reflexiveKind (alt1 : Bool := false) (alt2 : Bool := false)
      (zoneOrDamage : Bool := false) (targetOrReturn : Bool := false)
deriving Repr, Inhabited, BEq

namespace TriggerReflexiveKind

@[match_pattern] abbrev combatOrControlReflexive (trickArrows : Bool := false) (counterOrControl : Bool := false) : TriggerReflexiveKind :=
  .reflexiveKind trickArrows counterOrControl false false
@[match_pattern] abbrev zoneOrDamageReflexive (returnAttacking : Bool := false) (destroyOrDamage : Bool := false) : TriggerReflexiveKind :=
  .reflexiveKind returnAttacking destroyOrDamage true false
@[match_pattern] abbrev targetOrReturnReflexive (returnInstants : Bool := false) (plusOne : Bool := false) : TriggerReflexiveKind :=
  .reflexiveKind returnInstants plusOne false true
@[match_pattern] abbrev grantIndestructible : TriggerReflexiveKind := .combatOrControlReflexive false false
@[match_pattern] abbrev trickArrows : TriggerReflexiveKind := .combatOrControlReflexive true false
@[match_pattern] abbrev indestructibleCounter : TriggerReflexiveKind := .combatOrControlReflexive false true
@[match_pattern] abbrev controlOpponent : TriggerReflexiveKind := .combatOrControlReflexive true true
@[match_pattern] abbrev exileTopFive : TriggerReflexiveKind := .zoneOrDamageReflexive false false
@[match_pattern] abbrev returnAttacking : TriggerReflexiveKind := .zoneOrDamageReflexive true false
@[match_pattern] abbrev destroyOppNonland : TriggerReflexiveKind := .zoneOrDamageReflexive false true
@[match_pattern] abbrev countersDamage : TriggerReflexiveKind := .zoneOrDamageReflexive true true
@[match_pattern] abbrev hasteUnblockable : TriggerReflexiveKind := .targetOrReturnReflexive false false
@[match_pattern] abbrev returnInstants : TriggerReflexiveKind := .targetOrReturnReflexive true false
@[match_pattern] abbrev plusOne : TriggerReflexiveKind := .targetOrReturnReflexive false true

/-- The index `Resolution.mshReflexive` matches. -/
def toNat : TriggerReflexiveKind → Nat
  | .grantIndestructible => 0
  | .trickArrows => 2
  | .indestructibleCounter => 3
  | .controlOpponent => 4
  | .exileTopFive => 5
  | .returnAttacking => 6
  | .destroyOppNonland => 7
  | .countersDamage => 8
  | .hasteUnblockable => 9
  | .returnInstants => 11
  | _ => 12

end TriggerReflexiveKind

/-- Target-restriction and announced-target object selectors (CR 115). -/
inductive TargetObject where
  /-- Target-restriction or announced-target object selector (CR 115). -/
  | targetObjectKind (tyOpt : Option CardType := none) (subtype : Option String := none)
      (index : Option Nat := none) (alt1 : Bool := false) (alt2 : Bool := false)
      (alt3 : Bool := false) (eachOrSpecial : Bool := false) (permanentFlag : Bool := false)
      (typedOrIndexed : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace TargetObject

@[match_pattern] abbrev typedSubtypeOrIndexedTarget (tyOpt : Option CardType := none)
    (subtype : Option String := none) (index : Option Nat := none) : TargetObject :=
  .targetObjectKind tyOpt subtype index false false false false false true
@[match_pattern] abbrev ofCardType (ty : CardType := .creature) : TargetObject :=
  .typedSubtypeOrIndexedTarget (some ty) none none
@[match_pattern] abbrev anotherSubtype (subtype : String) : TargetObject :=
  .typedSubtypeOrIndexedTarget none (some subtype) none
@[match_pattern] abbrev targetAt (index : Nat) : TargetObject :=
  .typedSubtypeOrIndexedTarget none none (some index)
@[match_pattern] abbrev presenceOrAnnouncedTarget (alt1 : Bool := false) (alt2 : Bool := false) (announced : Bool := false) : TargetObject :=
  .targetObjectKind none none none alt1 alt2 announced false false false
@[match_pattern] abbrev eachPairOrSpecialTarget (alt1 : Bool := false) (alt2 : Bool := false) (special : Bool := false) : TargetObject :=
  .targetObjectKind none none none alt1 alt2 special true false false
@[match_pattern] abbrev permanent (byYou : Bool := false) : TargetObject :=
  .targetObjectKind none none none byYou false false false true false
@[match_pattern] abbrev targetPresence (ifPresent : Bool := false) (laterOrNextTurn : Bool := false) : TargetObject :=
  .presenceOrAnnouncedTarget ifPresent laterOrNextTurn false
@[match_pattern] abbrev announcedTarget (optional : Bool := false) (allOrFirstYours : Bool := false) : TargetObject :=
  .presenceOrAnnouncedTarget optional allOrFirstYours true
@[match_pattern] abbrev eachOrPairTarget (pair : Bool := false) (equipmentOnly : Bool := false) : TargetObject :=
  .eachPairOrSpecialTarget pair equipmentOnly false
@[match_pattern] abbrev specialCopyOrKickerTarget (legendOff : Bool := false) (kickerOrTwoTokens : Bool := false) : TargetObject :=
  .eachPairOrSpecialTarget legendOff kickerOrTwoTokens true

end TargetObject

/-- Permanent selectors on the battlefield (CR 110 / CR 403). -/
inductive BattlefieldObject where
  /-- Battlefield permanent selector kind across enchanted/combat, other/noted, source/group, attackers/pair, filtered, excluded/all, sacrifice/chosen-filter, cause/subtype, and card-type/plus-one permanents. -/
  | battlefieldObjectKind (subtype : Option String := none) (tyOpt : Option CardType := none)
      (whichOpt : Option YouControlPlusOne := none)
      (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (cat1 : Bool := false) (cat2 : Bool := false) (cat3 : Bool := false)
      (subtypeOrCauseFlag : Bool := false) (typeOrPlusOneFlag : Bool := false)
deriving Repr, Inhabited, BEq

namespace BattlefieldObject

@[match_pattern] abbrev subtypeOrCause (subtype : Option String := none) (nonSubtype : Bool := false)
    (withOpponents : Bool := false) (isCause : Bool := true) : BattlefieldObject :=
  .battlefieldObjectKind subtype none none nonSubtype withOpponents isCause false false false true false
@[match_pattern] abbrev typeOrPlusOneGroup (tyOpt : Option CardType := none) (opponents : Bool := false)
    (whichOpt : Option YouControlPlusOne := none) (isYouControl : Bool := false) : BattlefieldObject :=
  .battlefieldObjectKind none tyOpt whichOpt opponents isYouControl false false false false false true
@[match_pattern] abbrev cause (subtype : Option String := none) : BattlefieldObject :=
  .subtypeOrCause subtype false false true
@[match_pattern] abbrev subtypeFilter (subtype : String) (nonSubtype : Bool := false) (withOpponents : Bool := false) : BattlefieldObject :=
  .subtypeOrCause (some subtype) nonSubtype withOpponents false
@[match_pattern] abbrev permanentsOfType (ty : CardType := .creature) (opponents : Bool := false) : BattlefieldObject :=
  .typeOrPlusOneGroup (some ty) opponents none false
@[match_pattern] abbrev youControl (which : YouControlPlusOne := .eachCreature) : BattlefieldObject :=
  .typeOrPlusOneGroup none false (some which) true
@[match_pattern] abbrev enchantedOrCombatCreature (alt1 : Bool := false) (alt2 : Bool := false) (combatOrHaste : Bool := false) : BattlefieldObject :=
  .battlefieldObjectKind none none none alt1 alt2 combatOrHaste false false false false false
@[match_pattern] abbrev otherOrNotedPermanent (alt1 : Bool := false) (alt2 : Bool := false) (stepNoted : Bool := false) : BattlefieldObject :=
  .battlefieldObjectKind none none none alt1 alt2 stepNoted true false false false false
@[match_pattern] abbrev sourceOrGroupCreatures (alt1 : Bool := false) (alt2 : Bool := false) (groupOrTarget : Bool := false) : BattlefieldObject :=
  .battlefieldObjectKind none none none alt1 alt2 groupOrTarget false true false false false
@[match_pattern] abbrev attackersOrOppPair (alt1 : Bool := false) (alt2 : Bool := false) (oppOrPut : Bool := false) : BattlefieldObject :=
  .battlefieldObjectKind none none none alt1 alt2 oppOrPut true true false false false
@[match_pattern] abbrev filteredCreaturesYouControl (legendary : Bool := true) (withPlusOne : Bool := false) : BattlefieldObject :=
  .battlefieldObjectKind none none none legendary withPlusOne false false false true false false
@[match_pattern] abbrev excludedOrAllCreatures (alt1 : Bool := false) (alt2 : Bool := false) (allOrTokens : Bool := false) : BattlefieldObject :=
  .battlefieldObjectKind none none none alt1 alt2 allOrTokens true false true false false
@[match_pattern] abbrev sacrificeCopyOrChosenFilter (alt1 : Bool := false) (alt2 : Bool := false) (chosenOrTrample : Bool := false) : BattlefieldObject :=
  .battlefieldObjectKind none none none alt1 alt2 chosenOrTrample false true true false false
@[match_pattern] abbrev enchantedOrOppCreatures (oppCreatures : Bool := false) (flag : Bool := false) : BattlefieldObject :=
  .enchantedOrCombatCreature oppCreatures flag false
@[match_pattern] abbrev combatOrHasteCreature (attackingAlone : Bool := false) (monarchOrHaste : Bool := false) : BattlefieldObject :=
  .enchantedOrCombatCreature attackingAlone monarchOrHaste true
@[match_pattern] abbrev permanentsOfTypeYouControl (ty : CardType := .creature) : BattlefieldObject :=
  .permanentsOfType ty false
@[match_pattern] abbrev oppPermanents (ty : CardType := .artifact) : BattlefieldObject :=
  .permanentsOfType ty true
@[match_pattern] abbrev otherOrEquipmentYouControl (withArtifacts : Bool := false) (equipmentOrAny : Bool := false) : BattlefieldObject :=
  .otherOrNotedPermanent withArtifacts equipmentOrAny false
@[match_pattern] abbrev stepNotedPermanent (dealtDamage : Bool := false) (equipmentOrNotedHost : Bool := false) : BattlefieldObject :=
  .otherOrNotedPermanent dealtDamage equipmentOrNotedHost true
@[match_pattern] abbrev sourceOrTappedState (questCounters : Bool := false) (harnessedOrFirst : Bool := false) : BattlefieldObject :=
  .sourceOrGroupCreatures questCounters harnessedOrFirst false
@[match_pattern] abbrev groupOrTargetPlayerCreatures (humans : Bool := false) (equippedOrTargetPlayer : Bool := false) : BattlefieldObject :=
  .sourceOrGroupCreatures humans equippedOrTargetPlayer true
@[match_pattern] abbrev attackersFilter (untilYourTurn : Bool := false) (flag : Bool := false) : BattlefieldObject :=
  .attackersOrOppPair untilYourTurn flag false
@[match_pattern] abbrev oppPairOrPutArtifact (putArtifact : Bool := false) (flag : Bool := false) : BattlefieldObject :=
  .attackersOrOppPair putArtifact flag true
@[match_pattern] abbrev excludedOrGreatestPermanents (exceptYourTokens : Bool := false) (noFlyingOrGreatest : Bool := false) : BattlefieldObject :=
  .excludedOrAllCreatures exceptYourTokens noFlyingOrGreatest false
@[match_pattern] abbrev allCreaturesOrTokens (tokensOnly : Bool := false) (flag : Bool := false) : BattlefieldObject :=
  .excludedOrAllCreatures tokensOnly flag true
@[match_pattern] abbrev sacrificeChoiceOrSourceCopy (sourceCopy : Bool := false) (flag : Bool := false) : BattlefieldObject :=
  .sacrificeCopyOrChosenFilter sourceCopy flag false
@[match_pattern] abbrev chosenFilterOrTrampleAttackers (oddOrEven : Bool := false) (notChosenOrTrample : Bool := false) : BattlefieldObject :=
  .sacrificeCopyOrChosenFilter oddOrEven notChosenOrTrample true

end BattlefieldObject

/-- Card selectors in graveyards, exile, or noted across zones (CR 404 / CR 406). -/
inductive GraveyardExileObject where
  /-- Graveyard, discarded, linked exile, noted, copy-target, card-group, subtype, or MV/count-bounded selector. -/
  | graveyardExileKind (subtype : Option String := none) (n : Nat := 0) (tyOpt : Option CardType := none)
      (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false) (alt4 : Bool := false)
      (notedOrCopy : Bool := false) (cardGroup : Bool := false) (paramKind : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace GraveyardExileObject

@[match_pattern] abbrev paramGraveyardObject (subtype : Option String := none) (milledOnly : Bool := false)
    (n : Nat := 0) (creatureOnly : Bool := true) (orTeamwork : Bool := false) (instants : Bool := false)
    (tyOpt : Option CardType := none) (isCardOfType : Bool := false) : GraveyardExileObject :=
  .graveyardExileKind subtype n tyOpt milledOnly creatureOnly orTeamwork instants isCardOfType false true
@[match_pattern] abbrev subtypeInGraveyard (subtype : String) (milledOnly : Bool := false) : GraveyardExileObject :=
  .paramGraveyardObject (some subtype) milledOnly 0 true false false none false
@[match_pattern] abbrev natGraveyardObject (n : Nat) (creatureOnly : Bool := true) (orTeamwork : Bool := false) (instants : Bool := false) : GraveyardExileObject :=
  .paramGraveyardObject none false n creatureOnly orTeamwork instants none false
@[match_pattern] abbrev cardOfType (ty : CardType := .creature) : GraveyardExileObject :=
  .paramGraveyardObject none false 0 true false false (some ty) true
@[match_pattern] abbrev graveyardDiscardedOrLinked (alt1 : Bool := false) (alt2 : Bool := false) (linkedOrSpecial : Bool := false) : GraveyardExileObject :=
  .graveyardExileKind none 0 none alt1 alt2 linkedOrSpecial false false false false
@[match_pattern] abbrev notedOrCopyTarget (copyTarget : Bool := false) (flag : Bool := false) : GraveyardExileObject :=
  .graveyardExileKind none 0 none copyTarget flag false false true false false
@[match_pattern] abbrev graveyardCardGroup (modalTwo : Bool := false) (creaturesOnly : Bool := true) : GraveyardExileObject :=
  .graveyardExileKind none 0 none modalTwo creaturesOnly false false false true false
@[match_pattern] abbrev graveyardInstants (n : Nat) : GraveyardExileObject :=
  .natGraveyardObject n false false true
@[match_pattern] abbrev mvAtMost (mv : Nat) (creatureOnly : Bool := true) (orTeamwork : Bool := false) : GraveyardExileObject :=
  .natGraveyardObject mv creatureOnly orTeamwork false
@[match_pattern] abbrev graveyardOrDiscardedCard (discarded : Bool := false) (flag : Bool := false) : GraveyardExileObject :=
  .graveyardDiscardedOrLinked discarded flag false
@[match_pattern] abbrev linkedOrDiedOrSpecial (diedThisTurn : Bool := false) (outsideOrSphinx : Bool := false) : GraveyardExileObject :=
  .graveyardDiscardedOrLinked diedThisTurn outsideOrSphinx true

end GraveyardExileObject

/-- Card selectors in libraries and hands (CR 401 / CR 402). -/
inductive LibraryHandObject where
  /-- Hand, revealed, chosen, top/typed, or subtype/array card selector in libraries and hands (CR 401 / CR 402). -/
  | libraryHandKind (count : Option Nat := none) (s : Option Supertype := none)
      (tyOpt : Option CardType := none) (unlessCount : Option Nat := none)
      (subtypeOpt : Option String := none) (bound : Nat := 0) (typesOpt : Option (Array String) := none)
      (untapAt : Option Nat := none)
      (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false) (alt4 : Bool := false)
      (cardOrSpecial : Bool := false) (pilesOrLoot : Bool := false)
      (topOrTypedFlag : Bool := false) (subtypeOrArrayFlag : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace LibraryHandObject

@[match_pattern] abbrev topOrTypedCard (count : Option Nat := none) (opponentTop : Bool := false) (byPowerOrLands : Bool := false)
    (s : Option Supertype := none) (tyOpt : Option CardType := none) (fromHandOnly : Bool := false)
    (unlessCount : Option Nat := none) (isTyped : Bool := false) : LibraryHandObject :=
  .libraryHandKind count s tyOpt unlessCount none 0 none none opponentTop byPowerOrLands fromHandOnly isTyped false false true false
@[match_pattern] abbrev subtypeOrArrayLibraryHand (subtypeOpt : Option String := none) (bound : Nat := 0)
    (alt1 : Bool := false) (alt2 : Bool := false) (search : Bool := false)
    (typesOpt : Option (Array String) := none) (untapAt : Option Nat := none) (isArray : Bool := false) : LibraryHandObject :=
  .libraryHandKind none none none none subtypeOpt bound typesOpt untapAt alt1 alt2 search isArray false false false true
@[match_pattern] abbrev topOrLandsCount (count : Option Nat := none) (opponentTop : Bool := false) (byPowerOrLands : Bool := false) : LibraryHandObject :=
  .topOrTypedCard count opponentTop byPowerOrLands none none false none false
@[match_pattern] abbrev typedLibraryOrHandCard (s : Option Supertype := some .legendary) (ty : CardType := .creature) (fromHandOnly : Bool := false) : LibraryHandObject :=
  .topOrTypedCard none false false s (some ty) fromHandOnly none true
@[match_pattern] abbrev cardsUnlessType (n : Nat := 2) (ty : CardType := .artifact) : LibraryHandObject :=
  .topOrTypedCard none false false none (some ty) false (some n) false
@[match_pattern] abbrev subtypeLibraryHand (subtype : String) (bound : Nat := 0) (alt1 : Bool := false) (alt2 : Bool := false) (search : Bool := false) : LibraryHandObject :=
  .subtypeOrArrayLibraryHand (some subtype) bound alt1 alt2 search none none false
@[match_pattern] abbrev typesOrSubtypesArray (types : Array String) (untapAt : Option Nat := none) : LibraryHandObject :=
  .subtypeOrArrayLibraryHand none 0 false false false (some types) untapAt true
@[match_pattern] abbrev handRevealedOrChosenObject (alt1 : Bool := false) (alt2 : Bool := false) (chosenOrBasic : Bool := false) : LibraryHandObject :=
  .libraryHandKind none none none none none 0 none none alt1 alt2 chosenOrBasic false false false false false
@[match_pattern] abbrev handCardOrLibrarySpecial (alt1 : Bool := false) (alt2 : Bool := false) (special : Bool := false) : LibraryHandObject :=
  .libraryHandKind none none none none none 0 none none alt1 alt2 special false true false false false
@[match_pattern] abbrev pilesOrDrawDiscard (drawDiscard : Bool := false) (lootX : Bool := false) (flag : Bool := false) : LibraryHandObject :=
  .libraryHandKind none none none none none 0 none none drawDiscard lootX flag false false true false false
@[match_pattern] abbrev handOrRevealedObject (revealed : Bool := false) (cardFromHandOrRandom : Bool := false) : LibraryHandObject :=
  .handRevealedOrChosenObject revealed cardFromHandOrRandom false
@[match_pattern] abbrev chosenNonlandOrBasic (basicLand : Bool := false) (flag : Bool := false) : LibraryHandObject :=
  .handRevealedOrChosenObject basicLand flag true
@[match_pattern] abbrev subtypeWithBound (subtype : String) (bound : Nat) (creatureFromHand : Bool := false) : LibraryHandObject :=
  .subtypeLibraryHand subtype bound creatureFromHand false false
@[match_pattern] abbrev searchSubtype (subtype : String) (landOnly : Bool := true) (beholdUntap : Bool := false) : LibraryHandObject :=
  .subtypeLibraryHand subtype 0 landOnly beholdUntap true
@[match_pattern] abbrev cardOfTypeFromHand (ty : CardType := .land) : LibraryHandObject :=
  .typedLibraryOrHandCard none ty true
@[match_pattern] abbrev supertypeCard (s : Option Supertype := some .legendary) (ty : CardType := .creature) : LibraryHandObject :=
  .typedLibraryOrHandCard s ty false
@[match_pattern] abbrev card (nonlandOnly : Bool := false) (random : Bool := false) : LibraryHandObject :=
  .handCardOrLibrarySpecial nonlandOnly random false
@[match_pattern] abbrev libraryOrHandSpecial (artifactCreatureX : Bool := false) (oppLibOrShortfall : Bool := false) : LibraryHandObject :=
  .handCardOrLibrarySpecial artifactCreatureX oppLibOrShortfall true

end LibraryHandObject

/-- Sacrifice-choice and stack object selectors (CR 405 / CR 701.17). -/
inductive SacrificeStackObject where
  /-- Chosen creature (`false, false`), sacrifice target or stack reference (`true, false`), stack spell or ability (`false, true`), or sacrificed source (`sourceHow = some how`). -/
  | sacrificeOrStackKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (targetOrRef : Bool := false) (spellOrAbility : Bool := false)
      (sourceHow : Option SacrificeSourceHow := none)
deriving Repr, Inhabited, BEq

namespace SacrificeStackObject

@[match_pattern] abbrev sacrificedSource (how : SacrificeSourceHow := .isSacrificed) : SacrificeStackObject :=
  .sacrificeOrStackKind false false false false false (some how)
@[match_pattern] abbrev chosenCreature (opponentsOnly : Bool := false) (nontoken : Bool := false) (targetOpponent : Bool := false) : SacrificeStackObject :=
  .sacrificeOrStackKind opponentsOnly nontoken targetOpponent false false none
@[match_pattern] abbrev sacrificeTargetOrStackRef (alt1 : Bool := false) (alt2 : Bool := false) (stackRef : Bool := false) : SacrificeStackObject :=
  .sacrificeOrStackKind alt1 alt2 stackRef true false none
@[match_pattern] abbrev stackSpellOrAbility (ability : Bool := false) (copied : Bool := false) (flag : Bool := false) : SacrificeStackObject :=
  .sacrificeOrStackKind ability copied flag false true none
@[match_pattern] abbrev sacrificeTarget (combatDamager : Bool := false) (planOrAnother : Bool := false) : SacrificeStackObject :=
  .sacrificeTargetOrStackRef combatDamager planOrAnother false
@[match_pattern] abbrev castOrStackRef (spellTargets : Bool := false) (causingOrArchon : Bool := false) : SacrificeStackObject :=
  .sacrificeTargetOrStackRef spellTargets causingOrArchon true

end SacrificeStackObject

mutual

/-- Which player `ObjectSelector.player` names, who
`TriggerResolution.draw` draws for, who
`TriggerResolution.loseLife` loses life, who
`TriggerResolution.mill` mills, whose library
`TriggerResolution.revealLibrary` looks at, and who
`TriggerResolution.amass` amasses for.
An announced target is `.target`, and `which` is the `PlayerSelector`
restricting it. A player is `.target .player`.
The controllers of the objects an `ObjectSelector` names are `.controller`. -/
inductive PlayerSelector where
  /-- Seat, target-player, event/drain, indexed-target (`index = some idx`), or controller (`controllerOpt = some what`) player selector (`!eachOrHas && !targetKind && !eventOrDrain && index.isNone && controllerOpt.isNone`: you). -/
  | playerKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (eachOrHas : Bool := false) (targetKind : Bool := false) (eventOrDrain : Bool := false)
      (index : Option Nat := none) (controllerOpt : Option ObjectSelector)
  /-- The announced target `which` names. -/
  | target (which : PlayerSelector)
deriving Repr, Inhabited, BEq

/-- Who `TriggerResolution.pump` gives +P/+T until end of turn, who
`TriggerResolution.dealDamage` damages, what `TriggerResolution.discard`
discards, which cards `TriggerResolution.returnToHand` returns, which
permanent `TriggerResolution.sacrifice` sacrifices, who
`TriggerResolution.putCounters` puts counters on, who
`TriggerResolution.removeCounters` removes counters from, who
`TriggerResolution.tap` taps, who `TriggerResolution.untap` untaps,
which permanents `TriggerResolution.destroy` destroys, who
`TriggerResolution.grant` grants an ability to, who
`TriggerResolution.fight` uses, who
`TriggerResolution.lose` removes an ability from, who
`TriggerResolution.becomeArtifact` makes an artifact, who
`TriggerResolution.becomePrepared` prepares, who
`TriggerResolution.setBasePT` gives a new base power and toughness,
which card `TriggerResolution.putOnLibrary` puts on a library,
which cards `TriggerResolution.exile` exiles, and
which cards `TriggerResolution.put` puts onto the battlefield. -/
inductive ObjectSelector where
  /-- Leaf or player-relative object selector across source/any, target, battlefield, graveyard/exile, library/hand, sacrifice/stack, and player-relative objects. -/
  | leafObject (targetObjOpt : Option TargetObject := none)
      (bfObjOpt : Option BattlefieldObject := none)
      (gyObjOpt : Option GraveyardExileObject := none)
      (lhObjOpt : Option LibraryHandObject := none)
      (ssObjOpt : Option SacrificeStackObject := none)
      (whoOpt : Option PlayerSelector)
      (n : Nat := 0) (ty : Option CardType := none)
      (creatures : Bool := false) (cardsFlag : Bool := false) (wheel : Bool := false)
      (isAny : Bool := false)
  /-- Objects every selector (`isUnion = false, isTarget = false`) or any selector (`isUnion = true, isTarget = false`) in `what` names, or the announced target (`isTarget = true, what = [which]`). -/
  | combineOrTarget (what : List ObjectSelector) (isUnion : Bool := false) (isTarget : Bool := false)
deriving Repr, Inhabited, BEq

end

namespace PlayerSelector

@[match_pattern] abbrev controller (what : ObjectSelector) : PlayerSelector :=
  .playerKind false false false false false false none (some what)
@[match_pattern] abbrev targetAt (index : Nat) : PlayerSelector :=
  .playerKind false false false false false false (some index) none
@[match_pattern] abbrev you : PlayerSelector := .playerKind false false false false false false none none
@[match_pattern] abbrev eachOrHasYou (eachPlayer : Bool := false) (opponentHasYou : Bool := false) : PlayerSelector :=
  .playerKind eachPlayer opponentHasYou false true false false none none
@[match_pattern] abbrev targetPlayerKind (opponent : Bool := false) (announcedOrAll : Bool := false) : PlayerSelector :=
  .playerKind opponent announcedOrAll false false true false none none
@[match_pattern] abbrev eventOrDrainPlayer (damaged : Bool := false) (drain : Bool := false) (extortOrLose1 : Bool := false) : PlayerSelector :=
  .playerKind damaged drain extortOrLose1 false false true none none
@[match_pattern] abbrev eachOpponent : PlayerSelector := .eachOrHasYou false false
@[match_pattern] abbrev each : PlayerSelector := .eachOpponent
@[match_pattern] abbrev eachPlayer : PlayerSelector := .eachOrHasYou true false
@[match_pattern] abbrev opponentHasYou : PlayerSelector := .eachOrHasYou false true
@[match_pattern] abbrev player : PlayerSelector := .targetPlayerKind false false
@[match_pattern] abbrev recruit : PlayerSelector := .player
@[match_pattern] abbrev opponent : PlayerSelector := .targetPlayerKind true false
@[match_pattern] abbrev announced : PlayerSelector := .targetPlayerKind false true
@[match_pattern] abbrev targetPlayers : PlayerSelector := .targetPlayerKind true true
@[match_pattern] abbrev thatPlayer : PlayerSelector := .eventOrDrainPlayer false false false
@[match_pattern] abbrev damagedPlayer : PlayerSelector := .eventOrDrainPlayer true false false
@[match_pattern] abbrev youLose1Life : PlayerSelector := .eventOrDrainPlayer false false true
@[match_pattern] abbrev drainEachOpponent (extort : Bool := false) : PlayerSelector := .eventOrDrainPlayer false true extort
@[match_pattern] abbrev eachOpponentAndYouGain1 : PlayerSelector := .drainEachOpponent false
@[match_pattern] abbrev extort : PlayerSelector := .drainEachOpponent true

end PlayerSelector

namespace ObjectSelector

@[match_pattern] abbrev atomicObject (isAny : Bool := false) : ObjectSelector :=
  .leafObject none none none none none none 0 none false false false isAny
@[match_pattern] abbrev target (which : ObjectSelector := .leafObject none none none none none none 0 none false false false true) : ObjectSelector :=
  .combineOrTarget [which] false true
@[match_pattern] abbrev targetObj (o : TargetObject) : ObjectSelector :=
  .leafObject (some o) none none none none none 0 none false false false false
@[match_pattern] abbrev battlefield (o : BattlefieldObject) : ObjectSelector :=
  .leafObject none (some o) none none none none 0 none false false false false
@[match_pattern] abbrev graveyardExile (o : GraveyardExileObject) : ObjectSelector :=
  .leafObject none none (some o) none none none 0 none false false false false
@[match_pattern] abbrev libraryHand (o : LibraryHandObject) : ObjectSelector :=
  .leafObject none none none (some o) none none 0 none false false false false
@[match_pattern] abbrev sacrificeStack (o : SacrificeStackObject) : ObjectSelector :=
  .leafObject none none none none (some o) none 0 none false false false false
@[match_pattern] abbrev source : ObjectSelector := .atomicObject false
@[match_pattern] abbrev any : ObjectSelector := .atomicObject true
@[match_pattern] abbrev playerObjects (who : PlayerSelector) (n : Nat := 0) (ty : Option CardType := none)
    (creatures : Bool := false) (cardsFlag : Bool := false) (wheel : Bool := false) : ObjectSelector :=
  .leafObject none none none none none (some who) n ty creatures cardsFlag wheel false
@[match_pattern] abbrev player (who : PlayerSelector) : ObjectSelector :=
  .playerObjects who 0 none false false false
@[match_pattern] abbrev creaturesControlledBy (who : PlayerSelector) : ObjectSelector :=
  .playerObjects who 0 none true false false
@[match_pattern] abbrev graveyardCardsOfType (ty : CardType) (who : PlayerSelector) : ObjectSelector :=
  .playerObjects who 0 (some ty) false false false
@[match_pattern] abbrev cards (n : Nat := 1) (who : PlayerSelector := .you) : ObjectSelector :=
  .playerObjects who n none false true false
@[match_pattern] abbrev mayWheel (n : Nat) (who : PlayerSelector := .eachPlayer) : ObjectSelector :=
  .playerObjects who n none false false true
@[match_pattern] abbrev combine (what : List ObjectSelector) (isUnion : Bool := false) : ObjectSelector :=
  .combineOrTarget what isUnion false
@[match_pattern] abbrev intersection (what : List ObjectSelector) : ObjectSelector :=
  .combine what false
@[match_pattern] abbrev union (what : List ObjectSelector) : ObjectSelector :=
  .combine what true

-- TargetObject aliases
@[match_pattern] abbrev whileSource : ObjectSelector := .targetObj (.targetPresence false false)
@[match_pattern] abbrev ifPresent : ObjectSelector := .targetObj (.targetPresence true false)
@[match_pattern] abbrev creature : ObjectSelector := .targetObj (.ofCardType .creature)
@[match_pattern] abbrev laterCreature : ObjectSelector := .targetObj (.targetPresence false true)
@[match_pattern] abbrev planeswalker : ObjectSelector := .targetObj (.ofCardType .planeswalker)
@[match_pattern] abbrev anotherSubtype (subtype : String) : ObjectSelector := .targetObj (.anotherSubtype subtype)
@[match_pattern] abbrev eachPermanent : ObjectSelector := .targetObj (.eachOrPairTarget false false)
@[match_pattern] abbrev eachEquipment : ObjectSelector := .targetObj (.eachOrPairTarget false true)
@[match_pattern] abbrev permanent (byYou : Bool := false) : ObjectSelector := .targetObj (.permanent byYou)
@[match_pattern] abbrev announced : ObjectSelector := .targetObj (.announcedTarget false false)
@[match_pattern] abbrev announcedEquipment : ObjectSelector := .targetObj (.eachOrPairTarget true true)
@[match_pattern] abbrev optionalCreature : ObjectSelector := .targetObj (.announcedTarget true false)
@[match_pattern] abbrev announcedCreature : ObjectSelector := .targetObj (.eachOrPairTarget true false)
@[match_pattern] abbrev targetAt (index : Nat) : ObjectSelector := .targetObj (.targetAt index)
@[match_pattern] abbrev creatureTargets : ObjectSelector := .targetObj (.announcedTarget false true)
@[match_pattern] abbrev firstTargetCreatureYouControl : ObjectSelector := .targetObj (.announcedTarget true true)
@[match_pattern] abbrev secondArtifactTargetNotLegendary : ObjectSelector := .targetObj (.specialCopyOrKickerTarget false false)
@[match_pattern] abbrev targetLegendRuleOff : ObjectSelector := .targetObj (.specialCopyOrKickerTarget true false)
@[match_pattern] abbrev untilYourNextTurn : ObjectSelector := .targetObj (.targetPresence true true)
@[match_pattern] abbrev ownedCreaturesKicker : ObjectSelector := .targetObj (.specialCopyOrKickerTarget false true)
@[match_pattern] abbrev targetPermanentTwoTokensHasteSacrifice : ObjectSelector := .targetObj (.specialCopyOrKickerTarget true true)

-- BattlefieldObject aliases
@[match_pattern] abbrev enchanted : ObjectSelector := .battlefield (.enchantedOrOppCreatures false false)
@[match_pattern] abbrev cause (subtype : Option String := none) : ObjectSelector := .battlefield (.cause subtype)
@[match_pattern] abbrev creaturesYouControl : ObjectSelector := .battlefield (.permanentsOfTypeYouControl .creature)
@[match_pattern] abbrev othersOfSubtype (subtype : String) : ObjectSelector := .battlefield (.subtypeFilter subtype false false)
@[match_pattern] abbrev opponentsCreatures : ObjectSelector := .battlefield (.enchantedOrOppCreatures true false)
@[match_pattern] abbrev blockers : ObjectSelector := .battlefield (.combatOrHasteCreature false false)
@[match_pattern] abbrev eachNonSubtypeAndOpponents (subtype : String) : ObjectSelector := .battlefield (.subtypeFilter subtype true true)
@[match_pattern] abbrev youControl (which : YouControlPlusOne := .eachCreature) : ObjectSelector := .battlefield (.youControl which)
@[match_pattern] abbrev eachOther : ObjectSelector := .battlefield (.otherOrEquipmentYouControl false false)
@[match_pattern] abbrev createdToken : ObjectSelector := .battlefield (.stepNotedPermanent false false)
@[match_pattern] abbrev sourceIfPresent : ObjectSelector := .battlefield (.sourceOrTappedState false false)
@[match_pattern] abbrev eachUpToLastKnown : ObjectSelector := .battlefield (.groupOrTargetPlayerCreatures false false)
@[match_pattern] abbrev landsYouControl : ObjectSelector := .battlefield (.permanentsOfTypeYouControl .land)
@[match_pattern] abbrev humans : ObjectSelector := .battlefield (.groupOrTargetPlayerCreatures true false)
@[match_pattern] abbrev enchantedWhileSource : ObjectSelector := .battlefield (.enchantedOrOppCreatures false true)
@[match_pattern] abbrev attackingCreatures : ObjectSelector := .battlefield (.attackersFilter false false)
@[match_pattern] abbrev equipped : ObjectSelector := .battlefield (.groupOrTargetPlayerCreatures false true)
@[match_pattern] abbrev firstThisTurn : ObjectSelector := .battlefield (.sourceOrTappedState true true)
@[match_pattern] abbrev oppArtifactsEnchantments : ObjectSelector := .battlefield (.oppPairOrPutArtifact false false)
@[match_pattern] abbrev permanentDealtDamage : ObjectSelector := .battlefield (.stepNotedPermanent true false)
@[match_pattern] abbrev equippedAttackers : ObjectSelector := .battlefield (.attackersFilter false true)
@[match_pattern] abbrev attackingAlone : ObjectSelector := .battlefield (.combatOrHasteCreature true false)
@[match_pattern] abbrev equipmentHost : ObjectSelector := .battlefield (.stepNotedPermanent false true)
@[match_pattern] abbrev enteringVillain : ObjectSelector := .cause (some "Villain")
@[match_pattern] abbrev anyYouControl : ObjectSelector := .battlefield (.otherOrEquipmentYouControl true true)
@[match_pattern] abbrev putArtifact : ObjectSelector := .battlefield (.oppPairOrPutArtifact true false)
@[match_pattern] abbrev notedHost : ObjectSelector := .battlefield (.stepNotedPermanent true true)
@[match_pattern] abbrev enchantedCreature : ObjectSelector := .enchanted
@[match_pattern] abbrev legendaryCreaturesYouControl : ObjectSelector := .battlefield (.filteredCreaturesYouControl true false)
@[match_pattern] abbrev planeswalkersYouControl : ObjectSelector := .battlefield (.permanentsOfTypeYouControl .planeswalker)
@[match_pattern] abbrev forestsExceptCause : ObjectSelector := .battlefield (.excludedOrGreatestPermanents false false)
@[match_pattern] abbrev questCounters : ObjectSelector := .battlefield (.sourceOrTappedState true false)
@[match_pattern] abbrev putEquipment : ObjectSelector := .battlefield (.oppPairOrPutArtifact true true)
@[match_pattern] abbrev harnessedSource : ObjectSelector := .battlefield (.sourceOrTappedState false true)
@[match_pattern] abbrev artifact : ObjectSelector := .battlefield (.permanentsOfTypeYouControl .artifact)
@[match_pattern] abbrev anotherCreatureOrArtifact : ObjectSelector := .battlefield (.otherOrEquipmentYouControl true false)
@[match_pattern] abbrev allCreatures : ObjectSelector := .battlefield (.allCreaturesOrTokens false false)
@[match_pattern] abbrev creaturesOfTargetPlayer : ObjectSelector := .battlefield (.groupOrTargetPlayerCreatures true true)
@[match_pattern] abbrev nonSubtypeCreatures (subtype : String) : ObjectSelector := .battlefield (.subtypeFilter subtype true false)
@[match_pattern] abbrev oppCreaturesAndPlaneswalkers : ObjectSelector := .battlefield (.oppPairOrPutArtifact false true)
@[match_pattern] abbrev creaturesExceptYourTokens : ObjectSelector := .battlefield (.excludedOrGreatestPermanents true false)
@[match_pattern] abbrev creaturesWithPlusOne : ObjectSelector := .battlefield (.filteredCreaturesYouControl false true)
@[match_pattern] abbrev wizardTokensExceptRecent : ObjectSelector := .battlefield (.allCreaturesOrTokens true true)
@[match_pattern] abbrev tokensYouControl : ObjectSelector := .battlefield (.allCreaturesOrTokens true false)
@[match_pattern] abbrev creaturesWithoutFlying : ObjectSelector := .battlefield (.excludedOrGreatestPermanents false true)
@[match_pattern] abbrev land : ObjectSelector := .battlefield (.sacrificeChoiceOrSourceCopy false false)
@[match_pattern] abbrev creatureOrPlaneswalker : ObjectSelector := .battlefield (.sacrificeChoiceOrSourceCopy false true)
@[match_pattern] abbrev oppPermanents (ty : CardType := .artifact) : ObjectSelector := .battlefield (.oppPermanents ty)
@[match_pattern] abbrev sourceTwoNonlegendaryTokens : ObjectSelector := .battlefield (.sacrificeChoiceOrSourceCopy true true)
@[match_pattern] abbrev nontokenCreaturesYouControl : ObjectSelector := .battlefield (.filteredCreaturesYouControl false false)
@[match_pattern] abbrev sourceIfNotToken : ObjectSelector := .battlefield (.sacrificeChoiceOrSourceCopy true false)
@[match_pattern] abbrev allCreaturesExceptTwoChosen : ObjectSelector := .battlefield (.chosenFilterOrTrampleAttackers false false)
@[match_pattern] abbrev otherCreaturesOddOrEvenMv : ObjectSelector := .battlefield (.chosenFilterOrTrampleAttackers true false)
@[match_pattern] abbrev creaturesNotChosenType : ObjectSelector := .battlefield (.chosenFilterOrTrampleAttackers false true)
@[match_pattern] abbrev oppGreatestMvCreatureOrPlaneswalker : ObjectSelector := .battlefield (.excludedOrGreatestPermanents true true)
@[match_pattern] abbrev attackersOfCauseControllerWithTrample : ObjectSelector := .battlefield (.chosenFilterOrTrampleAttackers true true)
@[match_pattern] abbrev attackersAgainstYouUntilYourTurn : ObjectSelector := .battlefield (.attackersFilter true false)
@[match_pattern] abbrev attackersAgainstOpponentsUntilYourTurn : ObjectSelector := .battlefield (.attackersFilter true true)
@[match_pattern] abbrev equipmentYouControl : ObjectSelector := .battlefield (.otherOrEquipmentYouControl false true)
@[match_pattern] abbrev oppTappedCreatures : ObjectSelector := .battlefield (.enchantedOrOppCreatures true true)
@[match_pattern] abbrev creaturesPowerAtLeast4 : ObjectSelector := .battlefield (.allCreaturesOrTokens false true)
@[match_pattern] abbrev combatDamagerIfMonarch : ObjectSelector := .battlefield (.combatOrHasteCreature false true)
@[match_pattern] abbrev anyCreatureOnBattlefieldWithHaste : ObjectSelector := .battlefield (.combatOrHasteCreature true true)

-- GraveyardExileObject aliases
@[match_pattern] abbrev graveyardCard : ObjectSelector := .graveyardExile (.graveyardOrDiscardedCard false false)
@[match_pattern] abbrev graveyardPermanent : ObjectSelector := .graveyardExile (.graveyardOrDiscardedCard false true)
@[match_pattern] abbrev milledSubtype (subtype : String) : ObjectSelector := .graveyardExile (.subtypeInGraveyard subtype true)
@[match_pattern] abbrev linkedExile : ObjectSelector := .graveyardExile (.linkedOrDiedOrSpecial false false)
@[match_pattern] abbrev graveyardInstants (n : Nat) : ObjectSelector := .graveyardExile (.graveyardInstants n)
@[match_pattern] abbrev discarded : ObjectSelector := .graveyardExile (.graveyardOrDiscardedCard true false)
@[match_pattern] abbrev nonlandMvAtMost (mv : Nat) : ObjectSelector := .graveyardExile (.mvAtMost mv false false)
@[match_pattern] abbrev notedLands : ObjectSelector := .graveyardExile (.notedOrCopyTarget false true)
@[match_pattern] abbrev discardedLand : ObjectSelector := .graveyardExile (.graveyardOrDiscardedCard true true)
@[match_pattern] abbrev creatureMvAtMost (mv : Nat) : ObjectSelector := .graveyardExile (.mvAtMost mv true false)
@[match_pattern] abbrev creatureCard : ObjectSelector := .graveyardExile (.cardOfType .creature)
@[match_pattern] abbrev artifactEnchantmentOrLand : ObjectSelector := .graveyardExile (.notedOrCopyTarget true false)
@[match_pattern] abbrev creatureOrGraveyardCard : ObjectSelector := .graveyardExile (.notedOrCopyTarget true true)
@[match_pattern] abbrev noted : ObjectSelector := .graveyardExile (.notedOrCopyTarget false false)
@[match_pattern] abbrev creatureCardsInGraveyard : ObjectSelector := .graveyardExile (.graveyardCardGroup false true)
@[match_pattern] abbrev graveyardSubtype (subtype : String) : ObjectSelector := .graveyardExile (.subtypeInGraveyard subtype false)
@[match_pattern] abbrev allNonlandPermanentsInGraveyard : ObjectSelector := .graveyardExile (.graveyardCardGroup false false)
@[match_pattern] abbrev landCard : ObjectSelector := .graveyardExile (.cardOfType .land)
@[match_pattern] abbrev creatureMvAtMostOrTeamwork (n : Nat) : ObjectSelector := .graveyardExile (.mvAtMost n true true)
@[match_pattern] abbrev upToTwoGyModal : ObjectSelector := .graveyardExile (.graveyardCardGroup true false)
@[match_pattern] abbrev creaturesDiedThisTurn : ObjectSelector := .graveyardExile (.linkedOrDiedOrSpecial true false)
@[match_pattern] abbrev outsideGameOpponentChoice : ObjectSelector := .graveyardExile (.linkedOrDiedOrSpecial false true)
@[match_pattern] abbrev sphinxsApproach : ObjectSelector := .graveyardExile (.linkedOrDiedOrSpecial true true)

-- LibraryHandObject aliases
@[match_pattern] abbrev hand : ObjectSelector := .libraryHand (.handOrRevealedObject false false)
@[match_pattern] abbrev chosenNonland : ObjectSelector := .libraryHand (.chosenNonlandOrBasic false false)
@[match_pattern] abbrev revealed : ObjectSelector := .libraryHand (.handOrRevealedObject true false)
@[match_pattern] abbrev basicLand : ObjectSelector := .libraryHand (.chosenNonlandOrBasic true false)
@[match_pattern] abbrev cardFromHand : ObjectSelector := .libraryHand (.handOrRevealedObject false true)
@[match_pattern] abbrev top : ObjectSelector := .libraryHand (.topOrLandsCount none false false)
@[match_pattern] abbrev basicUpTo (subtype : String) (max : Nat) : ObjectSelector := .libraryHand (.subtypeWithBound subtype max false)
@[match_pattern] abbrev opponentTop (n : Nat) : ObjectSelector := .libraryHand (.topOrLandsCount (some n) true false)
@[match_pattern] abbrev landFromHand : ObjectSelector := .libraryHand (.cardOfTypeFromHand .land)
@[match_pattern] abbrev artifactFromHand : ObjectSelector := .libraryHand (.cardOfTypeFromHand .artifact)
@[match_pattern] abbrev randomCreature : ObjectSelector := .libraryHand (.handOrRevealedObject true true)
@[match_pattern] abbrev forest : ObjectSelector := .libraryHand (.searchSubtype "Forest" false false)
@[match_pattern] abbrev basicLandOnTop : ObjectSelector := .libraryHand (.chosenNonlandOrBasic true true)
@[match_pattern] abbrev dragon : ObjectSelector := .libraryHand (.searchSubtype "Dragon" false false)
@[match_pattern] abbrev creatureFromHand (subtype : String) (maxMv : Nat) : ObjectSelector := .libraryHand (.subtypeWithBound subtype maxMv true)
@[match_pattern] abbrev card : ObjectSelector := .libraryHand (.card false false)
@[match_pattern] abbrev nonland : ObjectSelector := .libraryHand (.card true false)
@[match_pattern] abbrev chosenNonlandPermanent : ObjectSelector := .libraryHand (.chosenNonlandOrBasic false true)
@[match_pattern] abbrev topPower : ObjectSelector := .libraryHand (.topOrLandsCount none false true)
@[match_pattern] abbrev landsUpTo (n : Nat) : ObjectSelector := .libraryHand (.topOrLandsCount (some n) true true)
@[match_pattern] abbrev landsEqualDamage : ObjectSelector := .libraryHand (.topOrLandsCount none true true)
@[match_pattern] abbrev planeswalkerCard : ObjectSelector := .libraryHand (.supertypeCard none .planeswalker)
@[match_pattern] abbrev enchantmentCard : ObjectSelector := .libraryHand (.supertypeCard none .enchantment)
@[match_pattern] abbrev supertypeCard (s : Supertype := .legendary) (ty : CardType := .creature) : ObjectSelector := .libraryHand (.supertypeCard (some s) ty)
@[match_pattern] abbrev landSubtype (subtype : String) : ObjectSelector := .libraryHand (.searchSubtype subtype true false)
@[match_pattern] abbrev basicBeholdUntap (subtype : String) : ObjectSelector := .libraryHand (.searchSubtype subtype true true)
@[match_pattern] abbrev basicLandsDifferentNamesX : ObjectSelector := .libraryHand (.libraryOrHandSpecial false false)
@[match_pattern] abbrev artifactCreatureX : ObjectSelector := .libraryHand (.libraryOrHandSpecial true false)
@[match_pattern] abbrev random : ObjectSelector := .libraryHand (.card false true)
@[match_pattern] abbrev topN (n : Nat) : ObjectSelector := .libraryHand (.topOrLandsCount (some n) false false)
@[match_pattern] abbrev opponentTopX : ObjectSelector := .libraryHand (.topOrLandsCount none true false)
@[match_pattern] abbrev lookedTypes (types : Array String) : ObjectSelector := .libraryHand (.typesOrSubtypesArray types none)
@[match_pattern] abbrev twoPiles : ObjectSelector := .libraryHand (.pilesOrDrawDiscard false false false)
@[match_pattern] abbrev cardsUnlessType (n : Nat := 2) (ty : CardType := .artifact) : ObjectSelector := .libraryHand (.cardsUnlessType n ty)
@[match_pattern] abbrev opponentLibrariesButBottom : ObjectSelector := .libraryHand (.libraryOrHandSpecial false true)
@[match_pattern] abbrev drawTwoDiscardTwoStun : ObjectSelector := .libraryHand (.pilesOrDrawDiscard true false true)
@[match_pattern] abbrev eachOpponentTwoDrawPerNonlandShortfall : ObjectSelector := .libraryHand (.libraryOrHandSpecial true true)
@[match_pattern] abbrev lootThenCountersPerDiscard : ObjectSelector := .libraryHand (.pilesOrDrawDiscard false true false)
@[match_pattern] abbrev drawAndDiscardXCreateSpiritPerType : ObjectSelector := .libraryHand (.pilesOrDrawDiscard false true true)
@[match_pattern] abbrev basicSubtypesUntapAt (kinds : Array String) (untapAt : Nat) : ObjectSelector := .libraryHand (.typesOrSubtypesArray kinds (some untapAt))
@[match_pattern] abbrev drawOneDiscardOne : ObjectSelector := .libraryHand (.pilesOrDrawDiscard true false false)
@[match_pattern] abbrev factOrFiction : ObjectSelector := .libraryHand (.pilesOrDrawDiscard false false true)

-- SacrificeStackObject aliases
@[match_pattern] abbrev opponentChosenCreature : ObjectSelector := .sacrificeStack (.chosenCreature true false true)
@[match_pattern] abbrev eachPlayersCreature : ObjectSelector := .sacrificeStack (.chosenCreature false false false)
@[match_pattern] abbrev leastPower : ObjectSelector := .sacrificeStack (.sacrificeTarget false false)
@[match_pattern] abbrev combatDamager : ObjectSelector := .sacrificeStack (.sacrificeTarget true false)
@[match_pattern] abbrev sacrificedSource (how : SacrificeSourceHow := .isSacrificed) : ObjectSelector := .sacrificeStack (.sacrificedSource how)
@[match_pattern] abbrev plan : ObjectSelector := .sacrificeStack (.sacrificeTarget false true)
@[match_pattern] abbrev another : ObjectSelector := .sacrificeStack (.sacrificeTarget true true)
@[match_pattern] abbrev chosenNontokenCreature : ObjectSelector := .sacrificeStack (.chosenCreature true true false)
@[match_pattern] abbrev youIfCast : ObjectSelector := .sacrificeStack (.castOrStackRef false false)
@[match_pattern] abbrev spellTargets : ObjectSelector := .sacrificeStack (.castOrStackRef true false)
@[match_pattern] abbrev eachOpponentsCreature : ObjectSelector := .sacrificeStack (.chosenCreature true false false)
@[match_pattern] abbrev targetSpell : ObjectSelector := .sacrificeStack (.stackSpellOrAbility false false false)
@[match_pattern] abbrev stackAbility (fromCreature : Bool := true) : ObjectSelector := .sacrificeStack (.stackSpellOrAbility true false fromCreature)
@[match_pattern] abbrev sourceSpellXTimes : ObjectSelector := .sacrificeStack (.stackSpellOrAbility false true false)
@[match_pattern] abbrev nextSpellThisTurn : ObjectSelector := .sacrificeStack (.stackSpellOrAbility false true true)
@[match_pattern] abbrev causingSpell : ObjectSelector := .sacrificeStack (.castOrStackRef false true)
@[match_pattern] abbrev archonCruelty : ObjectSelector := .sacrificeStack (.castOrStackRef true true)
@[match_pattern] abbrev targetSpellTwice : ObjectSelector := .sacrificeStack (.stackSpellOrAbility false false true)

end ObjectSelector


/-- Characteristic, power/toughness, mana value, and counter numbers (CR 202.3 / CR 208). -/
inductive StatNumber where
  /-- Characteristic, power/toughness, mana value, or counter statistic selector. -/
  | statNumberKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (cat1 : Bool := false) (cat2 : Bool := false) (greatestToughnessFlag : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace StatNumber

@[match_pattern] abbrev sourceStatOrPlusOnes (alt : Bool := false) (plusOnes : Bool := false) : StatNumber :=
  .statNumberKind alt plusOnes false false false false
@[match_pattern] abbrev powerOrSpellStat (alt1 : Bool := false) (alt2 : Bool := false) (spellStat : Bool := false) : StatNumber :=
  .statNumberKind alt1 alt2 spellStat true false false
@[match_pattern] abbrev counterOrSymbolStat (charge : Bool := false) (blueSymbolsOrFlying : Bool := false) : StatNumber :=
  .statNumberKind charge blueSymbolsOrFlying false false true false
@[match_pattern] abbrev greatestStatSpecial (putCreatures : Bool := false) : StatNumber :=
  .statNumberKind putCreatures false false true true false
@[match_pattern] abbrev greatestToughness : StatNumber :=
  .statNumberKind false false false false false true
@[match_pattern] abbrev equalSourceStat (toughness : Bool := false) : StatNumber := .sourceStatOrPlusOnes toughness false
@[match_pattern] abbrev plusOneCounters (ofTarget : Bool := false) : StatNumber := .sourceStatOrPlusOnes ofTarget true
@[match_pattern] abbrev sourceOrTargetPower (lastKnown : Bool := false) (targetOrCause : Bool := false) : StatNumber :=
  .powerOrSpellStat lastKnown targetOrCause false
@[match_pattern] abbrev spellOrArtifactStat (spellMv : Bool := false) (manaSpentOrChosenX : Bool := false) : StatNumber :=
  .powerOrSpellStat spellMv manaSpentOrChosenX true
@[match_pattern] abbrev double : StatNumber := .powerOrSpellStat false false false
@[match_pattern] abbrev lastKnownPower : StatNumber := .powerOrSpellStat true false false
@[match_pattern] abbrev equalToTargetPower : StatNumber := .powerOrSpellStat false true false
@[match_pattern] abbrev causePower : StatNumber := .powerOrSpellStat true true false
@[match_pattern] abbrev greatestArtifactMv : StatNumber := .powerOrSpellStat false false true
@[match_pattern] abbrev spellManaValue : StatNumber := .powerOrSpellStat true false true
@[match_pattern] abbrev equalToManaSpent : StatNumber := .powerOrSpellStat false true true
@[match_pattern] abbrev chosenX : StatNumber := .powerOrSpellStat true true true
@[match_pattern] abbrev perBurden : StatNumber := .counterOrSymbolStat false false
@[match_pattern] abbrev perChargeCounter : StatNumber := .counterOrSymbolStat true false
@[match_pattern] abbrev blueManaSymbols : StatNumber := .counterOrSymbolStat false true
@[match_pattern] abbrev totalFlyingPower : StatNumber := .counterOrSymbolStat true true
@[match_pattern] abbrev greatestPowerAndLoseLife : StatNumber := .greatestStatSpecial false
@[match_pattern] abbrev greatestToughnessThenPutCreatures : StatNumber := .greatestStatSpecial true

end StatNumber

/-- Zone, permanent, subtype, and feature counts (CR 109 / CR 400). -/
inductive CountNumber where
  /-- Zone, library, graveyard, attachment, artifact, or land count (`!isParam`), or parameterized subtype/card-type/hand-size count (`isParam = true`). -/
  | countNumberKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (artifactsOrLands : Bool := false)
      (subtype : Option String := none) (tyOpt : Option CardType := none)
      (handSize : Option Nat := none) (isParam : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace CountNumber

@[match_pattern] abbrev paramCountNumber (subtype : Option String := none) (tyOpt : Option CardType := none)
    (handSize : Option Nat := none) : CountNumber :=
  .countNumberKind false false false false subtype tyOpt handSize true
@[match_pattern] abbrev subtypeCount (subtype : String) : CountNumber :=
  .paramCountNumber (some subtype) none none
@[match_pattern] abbrev perControlled (ty : CardType) : CountNumber :=
  .paramCountNumber none (some ty) none
@[match_pattern] abbrev upToHandSize (n : Nat) : CountNumber :=
  .paramCountNumber none none (some n)
@[match_pattern] abbrev zoneLibraryOrAttachedCount (alt1 : Bool := false) (alt2 : Bool := false) (libraryOrGy : Bool := false) : CountNumber :=
  .countNumberKind alt1 alt2 libraryOrGy false none none none false
@[match_pattern] abbrev artifactsOrLandsCount (alt : Bool := false) (lands : Bool := false) : CountNumber :=
  .countNumberKind alt lands false true none none none false
@[match_pattern] abbrev zoneOrAttachedCount (fatGraveyard : Bool := false) (attachedOrChosen : Bool := false) : CountNumber :=
  .zoneLibraryOrAttachedCount fatGraveyard attachedOrChosen false
@[match_pattern] abbrev libraryOrGraveyardCount (minusGy : Bool := false) (colorsOrPwTypes : Bool := false) : CountNumber :=
  .zoneLibraryOrAttachedCount minusGy colorsOrPwTypes true
@[match_pattern] abbrev oppArtifacts (damagedPlayerOnly : Bool := false) : CountNumber := .artifactsOrLandsCount damagedPlayerOnly false
@[match_pattern] abbrev landCount (opponent : Bool := false) : CountNumber := .artifactsOrLandsCount opponent true
@[match_pattern] abbrev perOtherCreature : CountNumber := .zoneLibraryOrAttachedCount false false false
@[match_pattern] abbrev perFatGraveyard : CountNumber := .zoneLibraryOrAttachedCount true false false
@[match_pattern] abbrev attachedEquipment : CountNumber := .zoneLibraryOrAttachedCount false true false
@[match_pattern] abbrev chosenCreatureType : CountNumber := .zoneLibraryOrAttachedCount true true false
@[match_pattern] abbrev libraryCards : CountNumber := .zoneLibraryOrAttachedCount false false true
@[match_pattern] abbrev minusGraveyardCards : CountNumber := .zoneLibraryOrAttachedCount true false true
@[match_pattern] abbrev colorsAmongOtherArtifacts : CountNumber := .zoneLibraryOrAttachedCount false true true
@[match_pattern] abbrev planeswalkerTypes : CountNumber := .zoneLibraryOrAttachedCount true true true
@[match_pattern] abbrev basicLandsYouControl : CountNumber := .artifactsOrLandsCount false true
@[match_pattern] abbrev opponentLands : CountNumber := .artifactsOrLandsCount true true

end CountNumber

/-- Step-noted and turn-history numbers (CR 608 / CR 700). -/
inductive TurnEventNumber where
  /-- Step-noted, damage-noted, or turn-accumulated number selector. -/
  | turnEventNumberKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (cat1 : Bool := false) (cat2 : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace TurnEventNumber

@[match_pattern] abbrev stepOrDamageNotedNumber (alt1 : Bool := false) (alt2 : Bool := false) (damageOrPower : Bool := false) : TurnEventNumber :=
  .turnEventNumberKind alt1 alt2 damageOrPower false false
@[match_pattern] abbrev turnCountNumber (otherSpellsMv : Bool := false) (lifeGainedOrDiscarded : Bool := false) : TurnEventNumber :=
  .turnEventNumberKind otherSpellsMv lifeGainedOrDiscarded false true false
@[match_pattern] abbrev milledByTargetPlayerThisTurn : TurnEventNumber :=
  .turnEventNumberKind false false false false true
@[match_pattern] abbrev turnDeathOrLifeLost (lifeLost : Bool := false) : TurnEventNumber :=
  .turnEventNumberKind lifeLost false false true true
@[match_pattern] abbrev stepNotedNumber (discardedHand : Bool := false) (tappedHumanOrDestroyed : Bool := false) : TurnEventNumber :=
  .stepOrDamageNotedNumber discardedHand tappedHumanOrDestroyed false
@[match_pattern] abbrev damageOrPowerNoted (notedExcess : Bool := false) (notedPowerOrRemoved : Bool := false) : TurnEventNumber :=
  .stepOrDamageNotedNumber notedExcess notedPowerOrRemoved true
@[match_pattern] abbrev perLookedAt : TurnEventNumber := .stepOrDamageNotedNumber false false false
@[match_pattern] abbrev discardedHand : TurnEventNumber := .stepOrDamageNotedNumber true false false
@[match_pattern] abbrev forEachTappedHuman : TurnEventNumber := .stepOrDamageNotedNumber false true false
@[match_pattern] abbrev forEachDestroyedThisWay : TurnEventNumber := .stepOrDamageNotedNumber true true false
@[match_pattern] abbrev thatManyLost : TurnEventNumber := .stepOrDamageNotedNumber false false true
@[match_pattern] abbrev notedExcess : TurnEventNumber := .stepOrDamageNotedNumber true false true
@[match_pattern] abbrev notedPower : TurnEventNumber := .stepOrDamageNotedNumber false true true
@[match_pattern] abbrev removedPlusOnes : TurnEventNumber := .stepOrDamageNotedNumber true true true
@[match_pattern] abbrev cardsDrawnThisTurn : TurnEventNumber := .turnCountNumber false false
@[match_pattern] abbrev otherSpellsManaValue : TurnEventNumber := .turnCountNumber true false
@[match_pattern] abbrev lifeGainedThisTurn : TurnEventNumber := .turnCountNumber false true
@[match_pattern] abbrev cardsDiscardedThisTurn : TurnEventNumber := .turnCountNumber true true
@[match_pattern] abbrev creaturesDiedThisTurn : TurnEventNumber := .turnDeathOrLifeLost false
@[match_pattern] abbrev lifeLostThisTurn : TurnEventNumber := .turnDeathOrLifeLost true

end TurnEventNumber

/-- Where one statistic of `TriggerResolution.pump` reads its bonus,
where `TriggerResolution.dealDamage` reads its amount, how many cards
`TriggerResolution.scry` looks at, how many cards `TriggerResolution.draw`
draws, where one statistic of `TriggerResolution.setBasePT` reads its
new base, how much life `TriggerResolution.gainLife` gains, how much
life `TriggerResolution.loseLife` loses, how many cards
`TriggerResolution.mill` mills, how many counters
`TriggerResolution.amass` puts on an Army, how many times
`TriggerResolution.addMana` adds its mana, how many tokens
`TriggerResolution.createTokens` creates, how many cards
`TriggerResolution.surveil` surveils, how many loyalty counters
`TriggerResolution.empowerJace` puts on a Jace token, how much less
`TriggerResolution.spellsCostLess` makes a spell cost, how many cards
`TriggerResolution.lookAtTopRevealTypes` looks at, and the base power
and toughness `TriggerResolution.becomePT` sets, how many permanents
`CostSelector.sacrifice` sacrifices, how many cards
`CostSelector.discard` discards, and each number
`ConditionSelector.atLeast` compares.
`.greatestPower` is first so a default resolution uses it.
`.count` is how many objects an `ObjectSelector` names.
`.cardsDrawnThisTurn` is how many cards the controller has drawn this turn.
`.libraryCards` is how many cards are in the controller's library.
`.fixed` is a fixed bonus, `n` damage, scry `n`, draw `n`, a base of `n`,
`n` life gained, `n` life lost, mill `n`, amass `n`, add mana
`n` times, or discard `n` cards. -/
inductive NumberSelector where
  /-- Unified number selector: greatestPower (all `none`), fixed `n` (`fixedN = some n`), object number (`objOpt = some (what, isPower, isLoyalty)`), stat (`statOpt = some s`), count (`countOpt = some c`), or turnEvent (`turnEventOpt = some e`). -/
  | numberSelectorKind (fixedN : Option Int := none)
      (objOpt : Option (ObjectSelector × Bool × Bool) := none)
      (statOpt : Option StatNumber := none)
      (countOpt : Option CountNumber := none) (turnEventOpt : Option TurnEventNumber := none)
deriving Repr, Inhabited, BEq

namespace NumberSelector

@[match_pattern] abbrev greatestPower : NumberSelector :=
  .numberSelectorKind none none none none none
@[match_pattern] abbrev fixed (n : Int) : NumberSelector :=
  .numberSelectorKind (some n) none none none none
@[match_pattern] abbrev objectNumber (what : ObjectSelector := .source) (isPower : Bool := false) (isLoyalty : Bool := false) : NumberSelector :=
  .numberSelectorKind none (some (what, isPower, isLoyalty)) none none none
@[match_pattern] abbrev stat (s : StatNumber) : NumberSelector :=
  .numberSelectorKind none none (some s) none none
@[match_pattern] abbrev countKind (c : CountNumber) : NumberSelector :=
  .numberSelectorKind none none none (some c) none
@[match_pattern] abbrev turnEvent (e : TurnEventNumber) : NumberSelector :=
  .numberSelectorKind none none none none (some e)
@[match_pattern] abbrev count (what : ObjectSelector) : NumberSelector :=
  .objectNumber what false false
@[match_pattern] abbrev power (of : ObjectSelector) : NumberSelector :=
  .objectNumber of true false
@[match_pattern] abbrev loyalty (of : ObjectSelector := .source) : NumberSelector :=
  .objectNumber of false true

-- StatNumber aliases
@[match_pattern] abbrev equalSourceToughness : NumberSelector := .stat (.equalSourceStat true)
@[match_pattern] abbrev equalSourcePower : NumberSelector := .stat (.equalSourceStat false)
@[match_pattern] abbrev double : NumberSelector := .stat .double
@[match_pattern] abbrev lastKnownPower : NumberSelector := .stat .lastKnownPower
@[match_pattern] abbrev sourcePower : NumberSelector := .stat .lastKnownPower
@[match_pattern] abbrev greatestArtifactMv : NumberSelector := .stat .greatestArtifactMv
@[match_pattern] abbrev spellManaValue : NumberSelector := .stat .spellManaValue
@[match_pattern] abbrev equalToManaSpent : NumberSelector := .stat .equalToManaSpent
@[match_pattern] abbrev plusOneCounters : NumberSelector := .stat (.plusOneCounters false)
@[match_pattern] abbrev equalToTargetPower : NumberSelector := .stat .equalToTargetPower
@[match_pattern] abbrev perBurden : NumberSelector := .stat .perBurden
@[match_pattern] abbrev perChargeCounter : NumberSelector := .stat .perChargeCounter
@[match_pattern] abbrev blueManaSymbols : NumberSelector := .stat .blueManaSymbols
@[match_pattern] abbrev chosenX : NumberSelector := .stat .chosenX
@[match_pattern] abbrev causePower : NumberSelector := .stat .causePower
@[match_pattern] abbrev greatestPowerAndLoseLife : NumberSelector := .stat .greatestPowerAndLoseLife
@[match_pattern] abbrev greatestToughnessThenPutCreatures : NumberSelector := .stat .greatestToughnessThenPutCreatures
@[match_pattern] abbrev totalFlyingPower : NumberSelector := .stat .totalFlyingPower
@[match_pattern] abbrev greatestToughness : NumberSelector := .stat .greatestToughness
@[match_pattern] abbrev targetPlusOneCounters : NumberSelector := .stat (.plusOneCounters true)

-- CountNumber aliases
@[match_pattern] abbrev perOtherCreature : NumberSelector := .countKind .perOtherCreature
@[match_pattern] abbrev subtypeCount (subtype : String) : NumberSelector := .countKind (.subtypeCount subtype)
@[match_pattern] abbrev perPlains : NumberSelector := .subtypeCount "Plains"
@[match_pattern] abbrev perFatGraveyard : NumberSelector := .countKind .perFatGraveyard
@[match_pattern] abbrev perControlled (ty : CardType) : NumberSelector := .countKind (.perControlled ty)
@[match_pattern] abbrev upToHandSize (n : Nat) : NumberSelector := .countKind (.upToHandSize n)
@[match_pattern] abbrev attachedEquipment : NumberSelector := .countKind .attachedEquipment
@[match_pattern] abbrev oppArtifacts : NumberSelector := .countKind (.oppArtifacts false)
@[match_pattern] abbrev damagedPlayerArtifacts : NumberSelector := .countKind (.oppArtifacts true)
@[match_pattern] abbrev chosenCreatureType : NumberSelector := .countKind .chosenCreatureType
@[match_pattern] abbrev perSubtype (subtype : String) : NumberSelector := .subtypeCount subtype
@[match_pattern] abbrev libraryCards : NumberSelector := .countKind .libraryCards
@[match_pattern] abbrev minusGraveyardCards : NumberSelector := .countKind .minusGraveyardCards
@[match_pattern] abbrev colorsAmongOtherArtifacts : NumberSelector := .countKind .colorsAmongOtherArtifacts
@[match_pattern] abbrev planeswalkerTypes : NumberSelector := .countKind .planeswalkerTypes
@[match_pattern] abbrev basicLandsYouControl : NumberSelector := .countKind .basicLandsYouControl
@[match_pattern] abbrev opponentLands : NumberSelector := .countKind .opponentLands

-- TurnEventNumber aliases
@[match_pattern] abbrev perLookedAt : NumberSelector := .turnEvent .perLookedAt
@[match_pattern] abbrev discardedHand : NumberSelector := .turnEvent .discardedHand
@[match_pattern] abbrev forEachTappedHuman : NumberSelector := .turnEvent .forEachTappedHuman
@[match_pattern] abbrev forEachDestroyedThisWay : NumberSelector := .turnEvent .forEachDestroyedThisWay
@[match_pattern] abbrev thatManyLost : NumberSelector := .turnEvent .thatManyLost
@[match_pattern] abbrev notedExcess : NumberSelector := .turnEvent .notedExcess
@[match_pattern] abbrev notedPower : NumberSelector := .turnEvent .notedPower
@[match_pattern] abbrev cardsDrawnThisTurn : NumberSelector := .turnEvent .cardsDrawnThisTurn
@[match_pattern] abbrev otherSpellsManaValue : NumberSelector := .turnEvent .otherSpellsManaValue
@[match_pattern] abbrev removedPlusOnes : NumberSelector := .turnEvent .removedPlusOnes
@[match_pattern] abbrev lifeGainedThisTurn : NumberSelector := .turnEvent .lifeGainedThisTurn
@[match_pattern] abbrev cardsDiscardedThisTurn : NumberSelector := .turnEvent .cardsDiscardedThisTurn
@[match_pattern] abbrev milledByTargetPlayerThisTurn : NumberSelector := .turnEvent .milledByTargetPlayerThisTurn
@[match_pattern] abbrev creaturesDiedThisTurn : NumberSelector := .turnEvent .creaturesDiedThisTurn
@[match_pattern] abbrev lifeLostThisTurn : NumberSelector := .turnEvent .lifeLostThisTurn

end NumberSelector

instance : Coe Nat NumberSelector where
  coe n := .fixed (Int.ofNat n)

instance : Coe Int NumberSelector where
  coe := .fixed

instance (n : Nat) : OfNat NumberSelector n where
  ofNat := .fixed (Int.ofNat n)

/-- What `TriggerResolution.pay` or a spell's additional cost pays (CR 118.8 / CR 601.2b).
`sacrifice` pays by sacrificing permanents.
`discard` pays by discarding cards.
`behold` pays by beholding a quality (CR 701.60).
`or` pays any one of its costs. -/
inductive CostSelector where
  /-- Pay `symbols` mana (`manaOpt = some symbols`), behold `quality` (`quality = some q`), no additional cost (`isNone = true`), or sacrifice / discard `n` objects `what` names (`nOpt = some n, whatOpt = some what`). -/
  | atomicCost (manaOpt : Option (Array ManaSymbol) := Option.none) (quality : Option String := Option.none)
      (isNone : Bool := false) (nOpt : Option NumberSelector := Option.none)
      (whatOpt : Option ObjectSelector := Option.none) (isDiscard : Bool := false)
  /-- Pay any one of `costs`. -/
  | or (costs : List CostSelector)
deriving Repr, Inhabited, BEq

namespace CostSelector

@[match_pattern] abbrev manaOrBehold (manaOpt : Option (Array ManaSymbol) := Option.none) (quality : Option String := Option.none)
    (isNone : Bool := false) : CostSelector :=
  .atomicCost manaOpt quality isNone Option.none Option.none false
@[match_pattern] abbrev objectCost (n : NumberSelector) (what : ObjectSelector) (isDiscard : Bool := false) : CostSelector :=
  .atomicCost Option.none Option.none false (some n) (some what) isDiscard
@[match_pattern] abbrev mana (symbols : Array ManaSymbol) : CostSelector :=
  .manaOrBehold (some symbols) Option.none false
@[match_pattern] abbrev behold (quality : String) : CostSelector :=
  .manaOrBehold Option.none (some quality) false
@[match_pattern] abbrev none : CostSelector :=
  .manaOrBehold Option.none Option.none true
@[match_pattern] abbrev sacrifice (n : NumberSelector) (what : ObjectSelector) : CostSelector :=
  .objectCost n what false
@[match_pattern] abbrev discard (n : NumberSelector) (what : ObjectSelector) : CostSelector :=
  .objectCost n what true
@[match_pattern] abbrev sacrificeCreature : CostSelector := .sacrifice (.fixed 1) .creature
@[match_pattern] abbrev sacrificeArtifactOrCreatureOnly : CostSelector :=
  .sacrifice (.fixed 1) .anotherCreatureOrArtifact
@[match_pattern] abbrev sacrificeArtifactOrCreatureOrPay (n : Nat) : CostSelector :=
  .or [.sacrifice (.fixed 1) .anotherCreatureOrArtifact, .mana #[.generic n]]
def sacrificeArtifactOrCreature (orPayGeneric : Option Nat := Option.none) : CostSelector :=
  match orPayGeneric with
  | some n => .sacrificeArtifactOrCreatureOrPay n
  | Option.none => .sacrificeArtifactOrCreatureOnly
@[match_pattern] abbrev sacrificeCreatureOrPlaneswalkerOrPay (n : Nat) : CostSelector :=
  .or [.sacrifice (.fixed 1) .creatureOrPlaneswalker, .mana #[.generic n]]
@[match_pattern] abbrev discardOrPay (n : Nat) : CostSelector :=
  .or [.discard (.fixed 1) .card, .mana #[.generic n]]
@[match_pattern] abbrev beholdOrPay (quality : String) (n : Nat) : CostSelector :=
  .or [.behold quality, .mana #[.generic n]]

end CostSelector

/-- Permanent, source, and target state conditions (CR 110 / CR 205 / CR 208). -/
inductive StateCondition where
  /-- Source/counter/cause/target state (`!isSubtype && !isNumeric`), subtype/array condition (`isSubtype = true`), or numeric/power bound (`isNumeric = true`). -/
  | stateConditionKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (causeOrTarget : Bool := false) (subtypeOpt : Option String := none) (subtypesOpt : Option (Array String) := none)
      (isSubtype : Bool := false)
      (n : Nat := 0) (power : Int := 0) (graveyardOrMv : Bool := false) (isPower : Bool := false)
      (isNumeric : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace StateCondition

@[match_pattern] abbrev subtypeOrArrayCondition (subtypeOpt : Option String := none) (subtypesOpt : Option (Array String) := none) : StateCondition :=
  .stateConditionKind false false false false subtypeOpt subtypesOpt true 0 0 false false false
@[match_pattern] abbrev numericBoundCondition (n : Nat := 0) (power : Int := 0) (alt1 : Bool := false) (alt2 : Bool := false)
    (graveyardOrMv : Bool := false) (isPower : Bool := false) : StateCondition :=
  .stateConditionKind alt1 alt2 false false none none false n power graveyardOrMv isPower true
@[match_pattern] abbrev subtype (subtype : String) : StateCondition :=
  .subtypeOrArrayCondition (some subtype) none
@[match_pattern] abbrev youControlAnySubtype (subtypes : Array String) : StateCondition :=
  .subtypeOrArrayCondition none (some subtypes)
@[match_pattern] abbrev natBoundCondition (n : Nat) (alt1 : Bool := false) (alt2 : Bool := false) (graveyardOrMv : Bool := false) : StateCondition :=
  .numericBoundCondition n 0 alt1 alt2 graveyardOrMv false
@[match_pattern] abbrev powerBoundCondition (n : Int) (anotherAtMost : Bool := false) (targetPower : Bool := false) : StateCondition :=
  .numericBoundCondition 0 n anotherAtMost targetPower false true
@[match_pattern] abbrev sourceOrCounterState (alt1 : Bool := false) (alt2 : Bool := false) (originOrCounters : Bool := false) : StateCondition :=
  .stateConditionKind alt1 alt2 originOrCounters false none none false 0 0 false false false
@[match_pattern] abbrev causeTargetOrLegendary (alt1 : Bool := false) (alt2 : Bool := false) (targetOrLegendary : Bool := false) : StateCondition :=
  .stateConditionKind alt1 alt2 targetOrLegendary true none none false 0 0 false false false
@[match_pattern] abbrev sourceState (hope : Bool := false) (equipmentOrPrepared : Bool := false) : StateCondition :=
  .sourceOrCounterState hope equipmentOrPrepared false
@[match_pattern] abbrev always : StateCondition := .sourceOrCounterState false false false
@[match_pattern] abbrev hopeOnSource : StateCondition := .sourceOrCounterState true false false
@[match_pattern] abbrev attachedEquipment : StateCondition := .sourceOrCounterState false true false
@[match_pattern] abbrev preparedSource : StateCondition := .sourceOrCounterState true true false
@[match_pattern] abbrev sourceOrigin (wasCast : Bool := false) : StateCondition := .sourceOrCounterState false wasCast true
@[match_pattern] abbrev objectHadCounters (onSource : Bool := false) : StateCondition := .sourceOrCounterState true onSource true
@[match_pattern] abbrev causeGreaterStat (toughness : Bool := false) : StateCondition :=
  .causeTargetOrLegendary toughness false false
@[match_pattern] abbrev youControlLegendary : StateCondition := .causeTargetOrLegendary false true false
@[match_pattern] abbrev targetState (tapped : Bool := false) : StateCondition :=
  .causeTargetOrLegendary tapped false true
@[match_pattern] abbrev targetDamaged : StateCondition := .causeTargetOrLegendary false false true
@[match_pattern] abbrev targetTapped : StateCondition := .causeTargetOrLegendary true false true
@[match_pattern] abbrev targetAttacking (nontokenOnly : Bool := false) : StateCondition :=
  .causeTargetOrLegendary nontokenOnly true true
@[match_pattern] abbrev boardAtLeast (n : Nat) (jaceLoyalty : Bool := false) : StateCondition :=
  .natBoundCondition n jaceLoyalty false false
@[match_pattern] abbrev youControlCreatureToughnessAtLeast (n : Nat) : StateCondition := .natBoundCondition n false false false
@[match_pattern] abbrev jaceLoyaltyAtLeast (n : Nat) : StateCondition := .natBoundCondition n true false false
@[match_pattern] abbrev graveyardAtLeast (n : Nat) (creaturesOnly : Bool := false) : StateCondition :=
  .natBoundCondition n creaturesOnly true false
@[match_pattern] abbrev mvAtMost (n : Nat) : StateCondition := .natBoundCondition n false false true
@[match_pattern] abbrev creaturePowerBound (n : Int) (anotherAtMost : Bool := false) : StateCondition :=
  .powerBoundCondition n anotherAtMost false
@[match_pattern] abbrev youControlCreatureWithPower (n : Int) : StateCondition := .powerBoundCondition n false false
@[match_pattern] abbrev anotherCreaturePowerAtMost (n : Int) : StateCondition := .powerBoundCondition n true false
@[match_pattern] abbrev targetPowerAtMost (power : Int) : StateCondition := .powerBoundCondition power false true

end StateCondition

/-- Turn history and spell cast conditions (CR 601.2 / CR 603). -/
inductive TurnHistoryCondition where
  /-- Scried/noncombat-damage (`false, false`), turn/spell-cast history (`true, false`), not cast from hand (`false, true`), subtype turn event (`subtype = some s`), or resolve/life-gained bound (`bound = some n`). -/
  | turnHistoryKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (turnOrCast : Bool := false) (notFromHandFlag : Bool := false)
      (subtype : Option String := none) (bound : Option Nat := none)
deriving Repr, Inhabited, BEq, DecidableEq

namespace TurnHistoryCondition

@[match_pattern] abbrev subtypeTurnEvent (subtype : String) (entered : Bool := false) : TurnHistoryCondition :=
  .turnHistoryKind entered false false false false (some subtype) none
@[match_pattern] abbrev resolveOrLifeAtLeast (n : Nat) (gainedLife : Bool := false) : TurnHistoryCondition :=
  .turnHistoryKind gainedLife false false false false none (some n)
@[match_pattern] abbrev scriedOrNoncombatDamage (alt : Bool := false) (noncombatDamage : Bool := false) : TurnHistoryCondition :=
  .turnHistoryKind alt noncombatDamage false false false none none
@[match_pattern] abbrev turnOrSpellCastHistory (alt1 : Bool := false) (alt2 : Bool := false) (spellCast : Bool := false) : TurnHistoryCondition :=
  .turnHistoryKind alt1 alt2 spellCast true false none none
@[match_pattern] abbrev notFromHand : TurnHistoryCondition :=
  .turnHistoryKind false false false false true none none
@[match_pattern] abbrev scriedThisTurn (surveil : Bool := false) : TurnHistoryCondition := .scriedOrNoncombatDamage surveil false
@[match_pattern] abbrev opponentDealtNoncombatDamage (lastTurn : Bool := false) : TurnHistoryCondition := .scriedOrNoncombatDamage lastTurn true
@[match_pattern] abbrev turnActionHistory (attackedTwo : Bool := false) (noSpellOrLoyalty : Bool := false) : TurnHistoryCondition :=
  .turnOrSpellCastHistory attackedTwo noSpellOrLoyalty false
@[match_pattern] abbrev spellCastHistory (fromGraveyard : Bool := false) (teamworkOrGift : Bool := false) : TurnHistoryCondition :=
  .turnOrSpellCastHistory fromGraveyard teamworkOrGift true
@[match_pattern] abbrev nthResolve (n : Nat) : TurnHistoryCondition := .resolveOrLifeAtLeast n false
@[match_pattern] abbrev gainedLifeAtLeast (n : Nat) : TurnHistoryCondition := .resolveOrLifeAtLeast n true
@[match_pattern] abbrev artifactEnteredThisTurn : TurnHistoryCondition := .turnOrSpellCastHistory false false false
@[match_pattern] abbrev youAttackedWithTwoOrMore : TurnHistoryCondition := .turnOrSpellCastHistory true false false
@[match_pattern] abbrev castNoSpellThisTurn : TurnHistoryCondition := .turnOrSpellCastHistory false true false
@[match_pattern] abbrev activatedLoyaltyThisTurn : TurnHistoryCondition := .turnOrSpellCastHistory true true false
@[match_pattern] abbrev manaSpent : TurnHistoryCondition := .turnOrSpellCastHistory false false true
@[match_pattern] abbrev castFromGraveyard : TurnHistoryCondition := .turnOrSpellCastHistory true false true
@[match_pattern] abbrev teamwork : TurnHistoryCondition := .turnOrSpellCastHistory false true true
@[match_pattern] abbrev giftPromised : TurnHistoryCondition := .turnOrSpellCastHistory true true true

end TurnHistoryCondition

/-- Earlier-step resolution note conditions (CR 608.2c). -/
inductive StepNoteCondition where
  /-- Permanent/effect step note (`!wasSacrificedFlag`), earlier-step sacrifice note (`wasSacrificedFlag`), or dealt damage to `subtype` (`subtype = some s`). -/
  | stepNoteKind (alt1 : Bool := false) (alt2 : Bool := false) (effectNote : Bool := false)
      (wasSacrificedFlag : Bool := false) (subtype : Option String := none)
deriving Repr, Inhabited, BEq, DecidableEq

namespace StepNoteCondition

@[match_pattern] abbrev dealtDamageToSubtype (subtype : String) : StepNoteCondition :=
  .stepNoteKind false false false false (some subtype)
@[match_pattern] abbrev permanentOrEffectStepNote (alt1 : Bool := false) (alt2 : Bool := false) (effectNote : Bool := false) : StepNoteCondition :=
  .stepNoteKind alt1 alt2 effectNote false none
@[match_pattern] abbrev wasSacrificed (plan : Bool := false) : StepNoteCondition :=
  .stepNoteKind plan false false true none
@[match_pattern] abbrev permanentStepNote (returned : Bool := false) (controlledDestroyedOrStory : Bool := false) : StepNoteCondition :=
  .permanentOrEffectStepNote returned controlledDestroyedOrStory false
@[match_pattern] abbrev effectStepNote (opponentsMilled : Bool := false) (revealedMvOrEnrage : Bool := false) : StepNoteCondition :=
  .permanentOrEffectStepNote opponentsMilled revealedMvOrEnrage true
@[match_pattern] abbrev removedHope : StepNoteCondition := .permanentOrEffectStepNote false false false
@[match_pattern] abbrev returnedPermanent : StepNoteCondition := .permanentOrEffectStepNote true false false
@[match_pattern] abbrev youControlledDestroyed : StepNoteCondition := .permanentOrEffectStepNote false true false
@[match_pattern] abbrev enduringStoryNoted : StepNoteCondition := .permanentOrEffectStepNote true true false
@[match_pattern] abbrev equipmentAttached : StepNoteCondition := .permanentOrEffectStepNote false false true
@[match_pattern] abbrev opponentsMilled : StepNoteCondition := .permanentOrEffectStepNote true false true
@[match_pattern] abbrev revealedManaValueAtMostLands : StepNoteCondition := .permanentOrEffectStepNote false true true
@[match_pattern] abbrev enrageGrantsCombat : StepNoteCondition := .permanentOrEffectStepNote true true true

end StepNoteCondition

/-- Unified condition vocabulary for resolution branching (`Resolution.if` / `Resolution.ifElse`, CR 608.2c),
activation restrictions (`ActivatedAbility.condition`, CR 602.5b),
intervening “if” clauses (`SharedTriggerOpts.condition`, CR 603.4), and
conditional cost reductions (`CostReduction.when`, CR 601.2f).
`not` negates another condition. `or` holds when any of its conditions hold.
`atLeast` holds when its first number is at least its second. -/
inductive ConditionSelector where
  /-- Atomic state (`stateOpt = some s`), turn-history (`turnHistoryOpt = some t`), step-note (`stepNoteOpt = some n`), or `left >= right` (`leftOpt = some left, rightOpt = some right`) condition. -/
  | atomicCondition (stateOpt : Option StateCondition := Option.none)
      (turnHistoryOpt : Option TurnHistoryCondition := Option.none)
      (stepNoteOpt : Option StepNoteCondition := Option.none)
      (leftOpt : Option NumberSelector := Option.none)
      (rightOpt : Option NumberSelector := Option.none)
  /-- Composite condition: `not` (`isNot = true, conds = [cond]`) or `or` (`isNot = false, conds = conds`). -/
  | combineCondition (conds : List ConditionSelector) (isNot : Bool := false)
deriving Repr, Inhabited, BEq

namespace ConditionSelector

@[match_pattern] abbrev not (cond : ConditionSelector) : ConditionSelector :=
  .combineCondition [cond] true
@[match_pattern] abbrev or (conds : List ConditionSelector) : ConditionSelector :=
  .combineCondition conds false
@[match_pattern] abbrev atLeast (left right : NumberSelector) : ConditionSelector :=
  .atomicCondition Option.none Option.none Option.none (some left) (some right)
@[match_pattern] abbrev state (s : StateCondition := .always) : ConditionSelector :=
  .atomicCondition (some s) Option.none Option.none Option.none Option.none
@[match_pattern] abbrev turnHistory (t : TurnHistoryCondition) : ConditionSelector :=
  .atomicCondition Option.none (some t) Option.none Option.none Option.none
@[match_pattern] abbrev stepNote (n : StepNoteCondition) : ConditionSelector :=
  .atomicCondition Option.none Option.none (some n) Option.none Option.none

-- StateCondition aliases
@[match_pattern] abbrev none : ConditionSelector := .state .always
@[match_pattern] abbrev hopeOnSource : ConditionSelector := .state .hopeOnSource
@[match_pattern] abbrev attachedEquipment : ConditionSelector := .state .attachedEquipment
@[match_pattern] abbrev causeGreaterPower : ConditionSelector := .state (.causeGreaterStat false)
@[match_pattern] abbrev causeGreaterToughness : ConditionSelector := .state (.causeGreaterStat true)
@[match_pattern] abbrev subtype (subtype : String) : ConditionSelector := .state (.subtype subtype)
@[match_pattern] abbrev mvAtMost (n : Nat) : ConditionSelector := .state (.mvAtMost n)
@[match_pattern] abbrev preparedSource : ConditionSelector := .state .preparedSource
@[match_pattern] abbrev ifNotPrepared : ConditionSelector := .not .preparedSource
@[match_pattern] abbrev ifThreeCreaturesDied : ConditionSelector := .atLeast .creaturesDiedThisTurn (.fixed 3)
@[match_pattern] abbrev youControlCreatureWithPower (n : Int) : ConditionSelector := .state (.youControlCreatureWithPower n)
@[match_pattern] abbrev anotherCreaturePowerAtMost (n : Int) : ConditionSelector := .state (.anotherCreaturePowerAtMost n)
@[match_pattern] abbrev youControlCreatureToughnessAtLeast (n : Nat) : ConditionSelector := .state (.youControlCreatureToughnessAtLeast n)
@[match_pattern] abbrev youControlLegendary : ConditionSelector := .state .youControlLegendary
@[match_pattern] abbrev graveyardAtLeast (n : Nat) : ConditionSelector := .state (.graveyardAtLeast n false)
@[match_pattern] abbrev gyCreaturesAtLeast (n : Nat) : ConditionSelector := .state (.graveyardAtLeast n true)
@[match_pattern] abbrev jaceLoyaltyAtLeast (n : Nat) : ConditionSelector := .state (.jaceLoyaltyAtLeast n)
@[match_pattern] abbrev sourceNotToken : ConditionSelector := .state (.sourceOrigin false)
@[match_pattern] abbrev sourceWasCast : ConditionSelector := .state (.sourceOrigin true)
@[match_pattern] abbrev causeHadCounters : ConditionSelector := .state (.objectHadCounters false)
@[match_pattern] abbrev sourceHasCounters : ConditionSelector := .state (.objectHadCounters true)
@[match_pattern] abbrev targetDamaged : ConditionSelector := .state .targetDamaged
@[match_pattern] abbrev targetTapped : ConditionSelector := .state .targetTapped
@[match_pattern] abbrev targetAttackingNontoken : ConditionSelector := .state (.targetAttacking true)
@[match_pattern] abbrev targetAttacking : ConditionSelector := .state (.targetAttacking false)
@[match_pattern] abbrev targetPowerAtMost (power : Int) : ConditionSelector := .state (.targetPowerAtMost power)
@[match_pattern] abbrev youControlAnySubtype (subtypes : Array String) : ConditionSelector :=
  .state (.youControlAnySubtype subtypes)
@[match_pattern] abbrev youControlSubtype (subtype : String) : ConditionSelector :=
  .youControlAnySubtype #[subtype]

-- TurnHistoryCondition aliases
@[match_pattern] abbrev attackedWithSubtype (subtype : String) : ConditionSelector := .turnHistory (.subtypeTurnEvent subtype false)
@[match_pattern] abbrev subtypeEntered (subtype : String) : ConditionSelector := .turnHistory (.subtypeTurnEvent subtype true)
@[match_pattern] abbrev nthResolve (n : Nat) : ConditionSelector := .turnHistory (.nthResolve n)
@[match_pattern] abbrev scriedThisTurn : ConditionSelector := .turnHistory (.scriedThisTurn false)
@[match_pattern] abbrev surveilledThisTurn : ConditionSelector := .turnHistory (.scriedThisTurn true)
@[match_pattern] abbrev artifactEnteredThisTurn : ConditionSelector := .turnHistory .artifactEnteredThisTurn
@[match_pattern] abbrev manaSpent : ConditionSelector := .turnHistory .manaSpent
@[match_pattern] abbrev castFromGraveyard : ConditionSelector := .turnHistory .castFromGraveyard
@[match_pattern] abbrev teamwork : ConditionSelector := .turnHistory .teamwork
@[match_pattern] abbrev giftPromised : ConditionSelector := .turnHistory .giftPromised
@[match_pattern] abbrev notFromHand : ConditionSelector := .turnHistory .notFromHand
@[match_pattern] abbrev gainedLifeAtLeast (n : Nat) : ConditionSelector := .turnHistory (.gainedLifeAtLeast n)
@[match_pattern] abbrev scriedOrSurveilledThisTurn : ConditionSelector := .or [.scriedThisTurn, .surveilledThisTurn]
@[match_pattern] abbrev youAttackedWithTwoOrMore : ConditionSelector := .turnHistory .youAttackedWithTwoOrMore
@[match_pattern] abbrev opponentDealtNoncombatDamage : ConditionSelector := .turnHistory (.opponentDealtNoncombatDamage false)
@[match_pattern] abbrev opponentDealtNoncombatDamageLastTurn : ConditionSelector := .turnHistory (.opponentDealtNoncombatDamage true)
@[match_pattern] abbrev twoCreaturesDiedThisTurn : ConditionSelector := .atLeast .creaturesDiedThisTurn (.fixed 2)
@[match_pattern] abbrev drewThreeThisTurn : ConditionSelector := .atLeast .cardsDrawnThisTurn (.fixed 3)
@[match_pattern] abbrev castNoSpellThisTurn : ConditionSelector := .turnHistory .castNoSpellThisTurn
@[match_pattern] abbrev activatedLoyaltyThisTurn : ConditionSelector := .turnHistory .activatedLoyaltyThisTurn

-- StepNoteCondition aliases
@[match_pattern] abbrev removedHope : ConditionSelector := .stepNote .removedHope
@[match_pattern] abbrev dealtDamageToSubtype (subtype : String) : ConditionSelector := .stepNote (.dealtDamageToSubtype subtype)
@[match_pattern] abbrev returnedPermanent : ConditionSelector := .stepNote .returnedPermanent
@[match_pattern] abbrev youControlledDestroyed : ConditionSelector := .stepNote .youControlledDestroyed
@[match_pattern] abbrev enduringStoryNoted : ConditionSelector := .stepNote .enduringStoryNoted
@[match_pattern] abbrev sourceWasSacrificed : ConditionSelector := .stepNote (.wasSacrificed false)
@[match_pattern] abbrev planWasSacrificed : ConditionSelector := .stepNote (.wasSacrificed true)
@[match_pattern] abbrev equipmentAttached : ConditionSelector := .stepNote .equipmentAttached
@[match_pattern] abbrev opponentsMilled : ConditionSelector := .stepNote .opponentsMilled
@[match_pattern] abbrev revealedManaValueAtMostLands : ConditionSelector := .stepNote .revealedManaValueAtMostLands
@[match_pattern] abbrev enrageGrantsCombat : ConditionSelector := .stepNote .enrageGrantsCombat

end ConditionSelector

/-- Printed cost reduction on a spell or activated ability (CR 601.2f / CR 602.2b). -/
inductive CostReduction where
  | costReductionKind (n : Nat := 0) (condOpt : Option ConditionSelector := Option.none)
      (amountOpt : Option NumberSelector := Option.none)
deriving Repr, Inhabited, BEq

namespace CostReduction

@[match_pattern] abbrev none : CostReduction :=
  .costReductionKind 0 Option.none Option.none
/-- Costs `n` generic mana less if `cond` holds. -/
@[match_pattern] abbrev when (n : Nat) (cond : ConditionSelector) : CostReduction :=
  .costReductionKind n (some cond) Option.none
/-- Costs `perUnit` generic mana less per unit of `amount`. -/
@[match_pattern] abbrev byAmount (amount : NumberSelector) (perUnit : Nat := 1) : CostReduction :=
  .costReductionKind perUnit Option.none (some amount)
@[match_pattern] abbrev ifCreatureDied (n : Nat) : CostReduction :=
  .when n (.atLeast .creaturesDiedThisTurn (.fixed 1))
@[match_pattern] abbrev ifTargetDamaged (n : Nat) : CostReduction :=
  .when n .targetDamaged
@[match_pattern] abbrev ifTargetTapped (n : Nat) : CostReduction :=
  .when n .targetTapped
@[match_pattern] abbrev ifTargetAttackingNontoken (n : Nat) : CostReduction :=
  .when n .targetAttackingNontoken
@[match_pattern] abbrev ifTargetAttacking (n : Nat) : CostReduction :=
  .when n .targetAttacking
@[match_pattern] abbrev ifYouControl (n : Nat) (subtype : String) : CostReduction :=
  .when n (.atLeast (.subtypeCount subtype) (.fixed 1))
@[match_pattern] abbrev ifGyCreaturesAtLeast (min : Nat) (n : Nat) : CostReduction :=
  .when n (.gyCreaturesAtLeast min)
@[match_pattern] abbrev equalFlyingPower : CostReduction :=
  .byAmount .totalFlyingPower
@[match_pattern] abbrev greatestPower : CostReduction :=
  .byAmount .greatestPower
@[match_pattern] abbrev greatestToughness : CostReduction :=
  .byAmount .greatestToughness
@[match_pattern] abbrev equalOppArtifacts : CostReduction :=
  .byAmount .oppArtifacts
@[match_pattern] abbrev perPlusOneOnTarget : CostReduction :=
  .byAmount .targetPlusOneCounters
@[match_pattern] abbrev ifYouControlLegendary (n : Nat) : CostReduction :=
  .when n .youControlLegendary
@[match_pattern] abbrev perEquipment (n : Nat) : CostReduction :=
  .byAmount (.perSubtype "Equipment") n
@[match_pattern] abbrev ifTargetPowerAtMost (n : Nat) (power : Int) : CostReduction :=
  .when n (.targetPowerAtMost power)

end CostReduction


/-- What `TriggerResolution.dealDamage` records for a later step. -/
inductive TriggerDamageNote where
  /-- Damage record (`!mode`) or damage distribution/rider (`mode`). -/
  | damageNoteKind (alt1 : Bool := false) (alt2 : Bool := false) (mode : Bool := false)
deriving Repr, Inhabited, BEq

namespace TriggerDamageNote

@[match_pattern] abbrev damageRecord (marked : Bool := false) (excessOrEquipped : Bool := false) : TriggerDamageNote :=
  .damageNoteKind marked excessOrEquipped false
@[match_pattern] abbrev damageMode (fromCause : Bool := false) (preallocatedOrMountain : Bool := false) : TriggerDamageNote :=
  .damageNoteKind fromCause preallocatedOrMountain true
@[match_pattern] abbrev none : TriggerDamageNote := .damageRecord false false
@[match_pattern] abbrev markedPermanent : TriggerDamageNote := .damageRecord true false
@[match_pattern] abbrev excess : TriggerDamageNote := .damageRecord false true
@[match_pattern] abbrev fromEquipped : TriggerDamageNote := .damageRecord true true
@[match_pattern] abbrev divided : TriggerDamageNote := .damageMode false false
@[match_pattern] abbrev fromCause : TriggerDamageNote := .damageMode true false
@[match_pattern] abbrev preallocated : TriggerDamageNote := .damageMode false true
@[match_pattern] abbrev addRedIfMountain : TriggerDamageNote := .damageMode true true
@[match_pattern] abbrev sacrificeNoteKind (forReflexive : Bool := false) (notedOrBeast : Bool := false) (eyeOfJace : Bool := false) : TriggerDamageNote :=
  .damageNoteKind forReflexive notedOrBeast eyeOfJace
@[match_pattern] abbrev sacrificeRecord (forReflexive : Bool := false) (notedOrBeast : Bool := false) : TriggerDamageNote :=
  .sacrificeNoteKind forReflexive notedOrBeast false
@[match_pattern] abbrev eyeOfJaceIfSevenInGy : TriggerDamageNote := .sacrificeNoteKind false false true
@[match_pattern] abbrev forReflexive : TriggerDamageNote := .sacrificeRecord true false
@[match_pattern] abbrev noted : TriggerDamageNote := .sacrificeRecord false true
@[match_pattern] abbrev ifYouDoCreateBeast : TriggerDamageNote := .sacrificeRecord true true
@[match_pattern] abbrev castFromKind (alt1 : Bool := false) (alt2 : Bool := false) (special : Bool := false) : TriggerDamageNote :=
  .damageNoteKind alt1 alt2 special
@[match_pattern] abbrev zoneCastOrigin (hand : Bool := false) (impulseOrNextRG : Bool := false) : TriggerDamageNote :=
  .castFromKind hand impulseOrNextRG false
@[match_pattern] abbrev specialCastOrigin (milled : Bool := false) (uldarosOrBoast : Bool := false) : TriggerDamageNote :=
  .castFromKind milled uldarosOrBoast true
@[match_pattern] abbrev graveyard : TriggerDamageNote := .zoneCastOrigin false false
@[match_pattern] abbrev hand : TriggerDamageNote := .zoneCastOrigin true false
@[match_pattern] abbrev impulse : TriggerDamageNote := .zoneCastOrigin false true
@[match_pattern] abbrev nextRedOrGreenCreature : TriggerDamageNote := .zoneCastOrigin true true
@[match_pattern] abbrev looked : TriggerDamageNote := .specialCastOrigin false false
@[match_pattern] abbrev milledSpell : TriggerDamageNote := .specialCastOrigin true false
@[match_pattern] abbrev uldarosGraveyardTypes : TriggerDamageNote := .specialCastOrigin false true
@[match_pattern] abbrev boastExiled : TriggerDamageNote := .specialCastOrigin true true
@[match_pattern] abbrev castMvKind (twiceWizards : Bool := false) (lastKnownOrAttacking : Bool := false) (causingSpell : Bool := false) : TriggerDamageNote :=
  .damageNoteKind twiceWizards lastKnownOrAttacking causingSpell
@[match_pattern] abbrev powerOrWizardLimit (twiceWizards : Bool := false) (lastKnownOrAttacking : Bool := false) : TriggerDamageNote :=
  .castMvKind twiceWizards lastKnownOrAttacking false
@[match_pattern] abbrev causingSpell : TriggerDamageNote := .castMvKind false false true
@[match_pattern] abbrev unlimited : TriggerDamageNote := .powerOrWizardLimit false false
@[match_pattern] abbrev twiceLegendaryWizards : TriggerDamageNote := .powerOrWizardLimit true false
@[match_pattern] abbrev lastKnown : TriggerDamageNote := .powerOrWizardLimit false true
@[match_pattern] abbrev greatestAttackingPower : TriggerDamageNote := .powerOrWizardLimit true true
@[match_pattern] abbrev putHowKind (tapped : Bool := false) (artifactOrOwner : Bool := false) (atNextEndStep : Bool := false) : TriggerDamageNote :=
  .damageNoteKind tapped artifactOrOwner atNextEndStep
@[match_pattern] abbrev battlefieldEntryState (tapped : Bool := false) (artifactOrOwner : Bool := false) : TriggerDamageNote :=
  .putHowKind tapped artifactOrOwner false
@[match_pattern] abbrev atNextEndStep : TriggerDamageNote := .putHowKind false false true
@[match_pattern] abbrev asPrinted : TriggerDamageNote := .battlefieldEntryState false false
@[match_pattern] abbrev tapped : TriggerDamageNote := .battlefieldEntryState true false
@[match_pattern] abbrev asArtifact : TriggerDamageNote := .battlefieldEntryState false true
@[match_pattern] abbrev underOwner : TriggerDamageNote := .battlefieldEntryState true true
@[match_pattern] abbrev destroyNoteKind (alt1 : Bool := false) (alt2 : Bool := false) (drawOrRider : Bool := false) : TriggerDamageNote :=
  .damageNoteKind alt1 alt2 drawOrRider
@[match_pattern] abbrev destroyRecord (countDestroyed : Bool := false) (forAmassOrToken : Bool := false) : TriggerDamageNote :=
  .destroyNoteKind countDestroyed forAmassOrToken false
@[match_pattern] abbrev drawIf (legendaryEnchantment : Bool := false) : TriggerDamageNote :=
  .destroyNoteKind legendaryEnchantment false true
@[match_pattern] abbrev destroyRider (gainLifeEach : Bool := false) : TriggerDamageNote :=
  .destroyNoteKind gainLifeEach true true
@[match_pattern] abbrev countDestroyed : TriggerDamageNote := .destroyNoteKind true false false
@[match_pattern] abbrev forAmass : TriggerDamageNote := .destroyNoteKind false true false
@[match_pattern] abbrev chosenToken : TriggerDamageNote := .destroyNoteKind true true false
@[match_pattern] abbrev drawIfNotAttacking : TriggerDamageNote := .destroyNoteKind false false true
@[match_pattern] abbrev drawIfLegendaryEnchantment : TriggerDamageNote := .destroyNoteKind true false true
@[match_pattern] abbrev controllerCreatesHuman : TriggerDamageNote := .destroyNoteKind false true true
@[match_pattern] abbrev gainLifeEach : TriggerDamageNote := .destroyNoteKind true true true
@[match_pattern] abbrev controlHowKind (alt1 : Bool := false) (alt2 : Bool := false) (multi : Bool := false) : TriggerDamageNote :=
  .damageNoteKind alt1 alt2 multi
@[match_pattern] abbrev controlDuration (whileSource : Bool := false) (nextTurnOrVillain : Bool := false) : TriggerDamageNote :=
  .controlHowKind whileSource nextTurnOrVillain false
@[match_pattern] abbrev multiControl (exchange : Bool := false) : TriggerDamageNote :=
  .controlHowKind exchange false true
@[match_pattern] abbrev untilEndOfTurn : TriggerDamageNote := .controlDuration false false
@[match_pattern] abbrev whileSourceRemains : TriggerDamageNote := .controlDuration true false
@[match_pattern] abbrev duringNextTurn : TriggerDamageNote := .controlDuration false true
@[match_pattern] abbrev untilEotOrNextIfVillain : TriggerDamageNote := .controlDuration true true
@[match_pattern] abbrev oppArtifacts : TriggerDamageNote := .multiControl false
@[match_pattern] abbrev exchangeTargets : TriggerDamageNote := .multiControl true

end TriggerDamageNote

/-- What `TriggerResolution.lose` removes. -/
inductive AbilitySelector where
  /-- Indestructible until end of turn (`allAbilities = false`), or all abilities while the source remains (`allAbilities = true`). -/
  | abilitySelectorKind (allAbilities : Bool := false)
deriving Repr, Inhabited, BEq

namespace AbilitySelector

@[match_pattern] abbrev indestructible : AbilitySelector := .abilitySelectorKind false
@[match_pattern] abbrev allAbilities : AbilitySelector := .abilitySelectorKind true
@[match_pattern] abbrev castCostKind (withoutPaying : Bool := false) : AbilitySelector := .abilitySelectorKind withoutPaying
@[match_pattern] abbrev pay : AbilitySelector := .castCostKind false
@[match_pattern] abbrev withoutPaying : AbilitySelector := .castCostKind true
@[match_pattern] abbrev castNoteKind (exileInstead : Bool := false) : AbilitySelector := .abilitySelectorKind exileInstead
@[match_pattern] abbrev none : AbilitySelector := .castNoteKind false
@[match_pattern] abbrev exileInstead : AbilitySelector := .castNoteKind true
@[match_pattern] abbrev revealCountKind (onePlusCreatureCards : Bool := false) : AbilitySelector := .abilitySelectorKind onePlusCreatureCards
@[match_pattern] abbrev hand : AbilitySelector := .revealCountKind false
@[match_pattern] abbrev onePlusCreatureCards : AbilitySelector := .revealCountKind true
@[match_pattern] abbrev mayWhenKind (ifYouDont : Bool := false) : AbilitySelector := .abilitySelectorKind ifYouDont
@[match_pattern] abbrev ifYouDo : AbilitySelector := .mayWhenKind false
@[match_pattern] abbrev ifYouDont : AbilitySelector := .mayWhenKind true

end AbilitySelector

/-- What `TriggerResolution.removeCounters` removes. -/
inductive TriggerRemoveWhat where
  /-- One hope counter (`all = false, upTo = none`), every counter (`all = true, upTo = none`), or up to `n` counters of the controller's choice (`upTo = some n`). -/
  | removeWhatKind (all : Bool := false) (upTo : Option Nat := none)
deriving Repr, Inhabited, BEq

namespace TriggerRemoveWhat

@[match_pattern] abbrev hopeOrAll (all : Bool := false) : TriggerRemoveWhat := .removeWhatKind all none
@[match_pattern] abbrev upTo (n : Nat) : TriggerRemoveWhat := .removeWhatKind false (some n)
@[match_pattern] abbrev hope : TriggerRemoveWhat := .hopeOrAll false
@[match_pattern] abbrev all : TriggerRemoveWhat := .hopeOrAll true

end TriggerRemoveWhat

/-- What `TriggerResolution.putCounters` puts. `ofKind` uses its `n`. -/
inductive CounterSelector where
  /-- `n` counters of `kind` / remove counters (`kindOpt = some kind` or `remove = some what`), or noted/special/copied/dynamic/proliferate counters (`kindOpt = none && remove = none`). -/
  | counterSelectorKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (copied : Bool := false) (dynamic : Bool := false)
      (proliferate : Option NumberSelector := none)
      (kindOpt : Option CounterKind := none) (n : Nat := 1)
      (remove : Option TriggerRemoveWhat := none)
deriving Repr, Inhabited, BEq

namespace CounterSelector

@[match_pattern] abbrev ofKind (kind : CounterKind) (n : Nat := 1) : CounterSelector :=
  .counterSelectorKind false false false false false none (some kind) n none
@[match_pattern] abbrev remove (what : TriggerRemoveWhat) : CounterSelector :=
  .counterSelectorKind false false false false false none none 1 (some what)
@[match_pattern] abbrev eachKindOnIt (times : NumberSelector := .fixed 1) : CounterSelector :=
  .counterSelectorKind false false false false false (some times) none 1 none
@[match_pattern] abbrev notedOrSpecialCounters (alt1 : Bool := false) (alt2 : Bool := false) (special : Bool := false) : CounterSelector :=
  .counterSelectorKind alt1 alt2 special false false none none 1 none
@[match_pattern] abbrev copiedCounters (fromCause : Bool := false) : CounterSelector :=
  .counterSelectorKind fromCause false false true false none none 1 none
@[match_pattern] abbrev plusOneDynamic (byHand : Bool := false) (byChosenX : Bool := false) (byGyThree : Bool := false) : CounterSelector :=
  .counterSelectorKind byHand byChosenX byGyThree false true none none 1 none
@[match_pattern] abbrev plusOneFromNote (sacrificedPower : Bool := false) (notedCount : Bool := false) : CounterSelector :=
  .notedOrSpecialCounters sacrificedPower notedCount false
@[match_pattern] abbrev specialCounterAction (missingKeywords : Bool := false) (minusOneGyOrStunLoyalty : Bool := false) : CounterSelector :=
  .notedOrSpecialCounters missingKeywords minusOneGyOrStunLoyalty true
@[match_pattern] abbrev plusOneLastKnownMv : CounterSelector := .notedOrSpecialCounters false false false
@[match_pattern] abbrev plusOneSacrificedPower : CounterSelector := .notedOrSpecialCounters true false false
@[match_pattern] abbrev plusOneNoted : CounterSelector := .notedOrSpecialCounters false true false
@[match_pattern] abbrev sourceCounters : CounterSelector := .copiedCounters false
@[match_pattern] abbrev causeCounters : CounterSelector := .copiedCounters true
@[match_pattern] abbrev plusOnePerLand : CounterSelector := .plusOneDynamic false false false
@[match_pattern] abbrev plusOneEqualToHand : CounterSelector := .plusOneDynamic true false false
@[match_pattern] abbrev plusOneChosenX : CounterSelector := .plusOneDynamic false true false
@[match_pattern] abbrev plusOnePerThreeGraveyardIfFromGy : CounterSelector := .plusOneDynamic false false true
@[match_pattern] abbrev honePerOpponent : CounterSelector := .notedOrSpecialCounters false false true
@[match_pattern] abbrev missingKeywordsFromTarget : CounterSelector := .notedOrSpecialCounters true false true
@[match_pattern] abbrev minusOneGreatestGraveyardMv : CounterSelector := .notedOrSpecialCounters false true true
@[match_pattern] abbrev stunRemovedLoyalty : CounterSelector := .notedOrSpecialCounters true true true

end CounterSelector

/-- What `TriggerResolution.createTokens` records or queues after the token exists. -/
inductive TriggerTokenNote where
  /-- Token follow-up (`false, false`), remember/conditional creation (`true, false`), or destroy/currency note (`false, true`). -/
  | tokenNoteKind (alt1 : Bool := false) (alt2 : Bool := false)
      (rememberOrCond : Bool := false) (destroyOrCurrency : Bool := false)
deriving Repr, Inhabited, BEq

namespace TriggerTokenNote

@[match_pattern] abbrev tokenFollowup (attachReflexive : Bool := false) (indestructibleOrMardu : Bool := false) : TriggerTokenNote :=
  .tokenNoteKind attachReflexive indestructibleOrMardu false false
@[match_pattern] abbrev rememberOrIfCondition (alt : Bool := false) (ifCond : Bool := false) : TriggerTokenNote :=
  .tokenNoteKind alt ifCond true false
@[match_pattern] abbrev destroyOrCurrencyNote (alt : Bool := false) (currency : Bool := false) : TriggerTokenNote :=
  .tokenNoteKind alt currency false true
@[match_pattern] abbrev none : TriggerTokenNote := .tokenFollowup false false
@[match_pattern] abbrev attachReflexive : TriggerTokenNote := .tokenFollowup true false
@[match_pattern] abbrev teamIndestructible : TriggerTokenNote := .tokenFollowup false true
@[match_pattern] abbrev ifNotMarduLifelinkHaste : TriggerTokenNote := .tokenFollowup true true
@[match_pattern] abbrev remember (invasion : Bool := false) : TriggerTokenNote := .rememberOrIfCondition invasion false
@[match_pattern] abbrev invasion : TriggerTokenNote := .rememberOrIfCondition true false
@[match_pattern] abbrev ifCondition (monarch : Bool := false) : TriggerTokenNote := .rememberOrIfCondition monarch true
@[match_pattern] abbrev ifGainedLife : TriggerTokenNote := .rememberOrIfCondition false true
@[match_pattern] abbrev ifMonarch : TriggerTokenNote := .rememberOrIfCondition true true
@[match_pattern] abbrev destroyOthersIfXAtLeast5 (gainXLife : Bool := false) : TriggerTokenNote := .destroyOrCurrencyNote gainXLife false
@[match_pattern] abbrev gainXLifeAndDestroyOthersIf5 : TriggerTokenNote := .destroyOrCurrencyNote true false
@[match_pattern] abbrev currencyOrLose1Life (lose1Life : Bool := false) : TriggerTokenNote := .destroyOrCurrencyNote lose1Life true
@[match_pattern] abbrev currencyReturn : TriggerTokenNote := .destroyOrCurrencyNote false true
@[match_pattern] abbrev lose1Life : TriggerTokenNote := .destroyOrCurrencyNote true true

end TriggerTokenNote

/-- How long `TriggerResolution.exile` lasts. -/
inductive TriggerExileHow where
  /-- Linked/immediate exile (`false, false`), exile duration (`true, false`), play-until (`false, true`), numeric exile follow-up (`followupCount = some n`), or play while you control `subtype` (`subtype = some s`). -/
  | exileHowKind (alt1 : Bool := false) (alt2 : Bool := false)
      (duration : Bool := false) (playUntilFlag : Bool := false)
      (followupCount : Option Nat := none) (subtype : Option String := none)
deriving Repr, Inhabited, BEq

namespace TriggerExileHow

@[match_pattern] abbrev exileNumericFollowup (n : Nat) (damageOpponents : Bool := false) (returnBriefly : Bool := false) : TriggerExileHow :=
  .exileHowKind damageOpponents returnBriefly false false (some n) none
@[match_pattern] abbrev playIfYouControlSubtype (subtype : String) : TriggerExileHow :=
  .exileHowKind false false false false none (some subtype)
@[match_pattern] abbrev linkedOrImmediateExile (flag : Bool := false) (returnImmediately : Bool := false) : TriggerExileHow :=
  .exileHowKind flag returnImmediately false false none none
@[match_pattern] abbrev exileDuration (forLater : Bool := false) (anyManaWhileExiled : Bool := false) : TriggerExileHow :=
  .exileHowKind forLater anyManaWhileExiled true false none none
@[match_pattern] abbrev playUntil (thisTurn : Bool := false) (forLife : Bool := false) : TriggerExileHow :=
  .exileHowKind thisTurn forLife false true none none
@[match_pattern] abbrev linkedToSource (returnWhenLeaves : Bool := false) : TriggerExileHow := .linkedOrImmediateExile returnWhenLeaves false
@[match_pattern] abbrev leaveTrigger : TriggerExileHow := .linkedOrImmediateExile false false
@[match_pattern] abbrev untilSourceLeaves : TriggerExileHow := .linkedOrImmediateExile true false
@[match_pattern] abbrev returnImmediately (tapped : Bool := false) : TriggerExileHow := .linkedOrImmediateExile tapped true
@[match_pattern] abbrev returnTapped : TriggerExileHow := .linkedOrImmediateExile true true
@[match_pattern] abbrev nextEndStep : TriggerExileHow := .exileDuration false false
@[match_pattern] abbrev forLater : TriggerExileHow := .exileDuration true false
@[match_pattern] abbrev anyManaWhileExiled : TriggerExileHow := .exileDuration false true
@[match_pattern] abbrev playUntilNextTurn : TriggerExileHow := .playUntil false false
@[match_pattern] abbrev playThisTurn : TriggerExileHow := .playUntil true false
@[match_pattern] abbrev playForLifeThisTurn : TriggerExileHow := .playUntil true true
@[match_pattern] abbrev mayCastUpTo (casts : Nat) : TriggerExileHow := .exileNumericFollowup casts false false
@[match_pattern] abbrev mayCastElseDamageOpponents (damage : Nat) : TriggerExileHow := .exileNumericFollowup damage true false
@[match_pattern] abbrev returnBrieflyIfMvAtMost (maxMv : Nat) : TriggerExileHow := .exileNumericFollowup maxMv false true

end TriggerExileHow

/-- What a later step of `TriggerResolution.exile` can read. -/
inductive TriggerExileNote where
  /-- Exile object/link (`false, false`), revealed cast (`true, false`), count/reveal creatures (`false, true`), spell exile note (`true, true`), or gain `teamworkLife` life if teamwork was paid (`teamworkLife = some life`). -/
  | exileNoteKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (cat1 : Bool := false) (cat2 : Bool := false) (teamworkLife : Option Nat := Option.none)
deriving Repr, Inhabited, BEq

namespace TriggerExileNote

@[match_pattern] abbrev gainLifeIfTeamwork (life : Nat) : TriggerExileNote :=
  .exileNoteKind false false false false false (some life)
@[match_pattern] abbrev objectOrLinkExileNote (alt1 : Bool := false) (alt2 : Bool := false) (linkOrSearch : Bool := false) : TriggerExileNote :=
  .exileNoteKind alt1 alt2 linkOrSearch false false Option.none
@[match_pattern] abbrev revealedCast (anyManaThisTurn : Bool := false) : TriggerExileNote :=
  .exileNoteKind anyManaThisTurn false false true false Option.none
@[match_pattern] abbrev countOrRevealCreaturesNote (flag : Bool := false) (revealToBf : Bool := false) : TriggerExileNote :=
  .exileNoteKind flag revealToBf false false true Option.none
@[match_pattern] abbrev exileSpellNote (worldsWithinWorlds : Bool := false) (revealOrDespark : Bool := false) (swordsLife : Bool := false) : TriggerExileNote :=
  .exileNoteKind worldsWithinWorlds revealOrDespark swordsLife true true Option.none
@[match_pattern] abbrev exileObjectNote (lands : Bool := false) (copyOrPlayCard : Bool := false) : TriggerExileNote :=
  .objectOrLinkExileNote lands copyOrPlayCard false
@[match_pattern] abbrev exileLinkOrSearchNote (ifHero : Bool := false) (searchBasicOrDraw3 : Bool := false) : TriggerExileNote :=
  .objectOrLinkExileNote ifHero searchBasicOrDraw3 true
@[match_pattern] abbrev none : TriggerExileNote := .objectOrLinkExileNote false false false
@[match_pattern] abbrev lands : TriggerExileNote := .objectOrLinkExileNote true false false
@[match_pattern] abbrev copyAndHost : TriggerExileNote := .objectOrLinkExileNote false true false
@[match_pattern] abbrev playCard : TriggerExileNote := .objectOrLinkExileNote true true false
@[match_pattern] abbrev impulse : TriggerExileNote := .revealedCast false
@[match_pattern] abbrev anyManaThisTurn : TriggerExileNote := .revealedCast true
@[match_pattern] abbrev linked : TriggerExileNote := .objectOrLinkExileNote false false true
@[match_pattern] abbrev ifHero : TriggerExileNote := .objectOrLinkExileNote true false true
@[match_pattern] abbrev controllerMaySearchBasic : TriggerExileNote := .objectOrLinkExileNote false true true
@[match_pattern] abbrev thenDrawThree : TriggerExileNote := .objectOrLinkExileNote true true true
@[match_pattern] abbrev countExiledCreatures (incubate : Bool := false) : TriggerExileNote := .countOrRevealCreaturesNote incubate false
@[match_pattern] abbrev empowerJace : TriggerExileNote := .countOrRevealCreaturesNote false false
@[match_pattern] abbrev incubateCount : TriggerExileNote := .countOrRevealCreaturesNote true false
@[match_pattern] abbrev revealCreaturesToBattlefield (atEndStep : Bool := false) : TriggerExileNote := .countOrRevealCreaturesNote atEndStep true
@[match_pattern] abbrev revealCreaturesAtEndStep : TriggerExileNote := .countOrRevealCreaturesNote true true
@[match_pattern] abbrev counteredPermanentMayCast : TriggerExileNote := .exileSpellNote false false false
@[match_pattern] abbrev worldsWithinWorlds : TriggerExileNote := .exileSpellNote true false false
@[match_pattern] abbrev revealUntilCreatureOrPlaneswalker : TriggerExileNote := .exileSpellNote false true false
@[match_pattern] abbrev despark : TriggerExileNote := .exileSpellNote true true false
@[match_pattern] abbrev controllerGainsLifePower : TriggerExileNote := .exileSpellNote false false true

end TriggerExileNote

/-- What a later step of `TriggerResolution.sacrifice` can read. -/
abbrev TriggerSacrificeNote := TriggerDamageNote

namespace TriggerSacrificeNote

@[match_pattern] abbrev sacrificeRecord (forReflexive : Bool := false) (notedOrBeast : Bool := false) : TriggerSacrificeNote :=
  .sacrificeNoteKind forReflexive notedOrBeast false
@[match_pattern] abbrev eyeOfJaceIfSevenInGy : TriggerSacrificeNote :=
  .sacrificeNoteKind false false true
@[match_pattern] abbrev none : TriggerSacrificeNote := .sacrificeRecord false false
@[match_pattern] abbrev forReflexive : TriggerSacrificeNote := .sacrificeRecord true false
@[match_pattern] abbrev noted : TriggerSacrificeNote := .sacrificeRecord false true
@[match_pattern] abbrev ifYouDoCreateBeast : TriggerSacrificeNote := .sacrificeRecord true true

end TriggerSacrificeNote

/-- Where `TriggerResolution.mayCast` finds the spell. -/
abbrev TriggerCastFrom := TriggerDamageNote

namespace TriggerCastFrom

@[match_pattern] abbrev zoneCastOrigin (hand : Bool := false) (impulseOrNextRG : Bool := false) : TriggerCastFrom :=
  .castFromKind hand impulseOrNextRG false
@[match_pattern] abbrev specialCastOrigin (milled : Bool := false) (uldarosOrBoast : Bool := false) : TriggerCastFrom :=
  .castFromKind milled uldarosOrBoast true
@[match_pattern] abbrev graveyard : TriggerCastFrom := .zoneCastOrigin false false
@[match_pattern] abbrev hand : TriggerCastFrom := .zoneCastOrigin true false
@[match_pattern] abbrev impulse : TriggerCastFrom := .zoneCastOrigin false true
@[match_pattern] abbrev nextRedOrGreenCreature : TriggerCastFrom := .zoneCastOrigin true true
@[match_pattern] abbrev looked : TriggerCastFrom := .specialCastOrigin false false
@[match_pattern] abbrev milledSpell : TriggerCastFrom := .specialCastOrigin true false
@[match_pattern] abbrev uldarosGraveyardTypes : TriggerCastFrom := .specialCastOrigin false true
@[match_pattern] abbrev boastExiled : TriggerCastFrom := .specialCastOrigin true true

end TriggerCastFrom

/-- The mana-value limit of `TriggerResolution.mayCast`.
`.unlimited` is no limit. -/
abbrev TriggerCastMv := TriggerDamageNote

namespace TriggerCastMv

@[match_pattern] abbrev powerOrWizardLimit (twiceWizards : Bool := false) (lastKnownOrAttacking : Bool := false) : TriggerCastMv :=
  .castMvKind twiceWizards lastKnownOrAttacking false
@[match_pattern] abbrev causingSpell : TriggerCastMv := .castMvKind false false true
@[match_pattern] abbrev unlimited : TriggerCastMv := .powerOrWizardLimit false false
@[match_pattern] abbrev twiceLegendaryWizards : TriggerCastMv := .powerOrWizardLimit true false
@[match_pattern] abbrev lastKnown : TriggerCastMv := .powerOrWizardLimit false true
@[match_pattern] abbrev greatestAttackingPower : TriggerCastMv := .powerOrWizardLimit true true

end TriggerCastMv

/-- Whether `TriggerResolution.mayCast` pays the mana cost. -/
abbrev TriggerCastCost := AbilitySelector

namespace TriggerCastCost

@[match_pattern] abbrev pay : TriggerCastCost := .castCostKind false
@[match_pattern] abbrev withoutPaying : TriggerCastCost := .castCostKind true

end TriggerCastCost

/-- What happens to an instant or sorcery `TriggerResolution.mayCast` casts. -/
abbrev TriggerCastNote := AbilitySelector

namespace TriggerCastNote

@[match_pattern] abbrev none : TriggerCastNote := .castNoteKind false
@[match_pattern] abbrev exileInstead : TriggerCastNote := .castNoteKind true

end TriggerCastNote

/-- What a later step of `TriggerResolution.returnToHand` can read. -/
abbrev TriggerReturnNote := AbilityCastKind

namespace TriggerReturnNote

@[match_pattern] abbrev none : TriggerReturnNote := .returnNoteKind false false
@[match_pattern] abbrev returnedPermanent : TriggerReturnNote := .returnNoteKind true false
@[match_pattern] abbrev delayedBirds : TriggerReturnNote := .returnNoteKind false true

end TriggerReturnNote

/-- How a card `TriggerResolution.put` changes as it enters. -/
inductive TriggerEnterWith where
  /-- Lose all abilities / enter attacking / gain `subtype` (`kOpt = none && kindOpt = none`), or gain `k` keywords (`kOpt = some k`) / put `n` counters of `kind` (`kindOpt = some kind`). -/
  | enterWithKind (attacking : Bool := false) (subtype : Option String := none)
      (kOpt : Option Keywords := none) (kindOpt : Option CounterKind := none)
      (n : Nat := 1) (asEnters : Bool := false)
deriving Repr, Inhabited, BEq

namespace TriggerEnterWith

@[match_pattern] abbrev enterStateOrSubtype (attacking : Bool := false) (subtype : Option String := none) : TriggerEnterWith :=
  .enterWithKind attacking subtype none none 1 false
@[match_pattern] abbrev loseAllAbilities : TriggerEnterWith := .enterStateOrSubtype false none
@[match_pattern] abbrev attacking : TriggerEnterWith := .enterStateOrSubtype true none
@[match_pattern] abbrev additionalSubtype (subtype : String) : TriggerEnterWith :=
  .enterStateOrSubtype false (some subtype)
@[match_pattern] abbrev keywords (k : Keywords) : TriggerEnterWith :=
  .enterWithKind false none (some k) none 1 false
@[match_pattern] abbrev counter (kind : CounterKind) (n : Nat := 1) (asEnters : Bool := false) : TriggerEnterWith :=
  .enterWithKind false none none (some kind) n asEnters

end TriggerEnterWith

/-- How `TriggerResolution.put` puts those cards onto the battlefield. -/
abbrev TriggerPutHow := TriggerDamageNote

namespace TriggerPutHow

@[match_pattern] abbrev battlefieldEntryState (tapped : Bool := false) (artifactOrOwner : Bool := false) : TriggerPutHow :=
  .putHowKind tapped artifactOrOwner false
@[match_pattern] abbrev atNextEndStep : TriggerPutHow := .putHowKind false false true
@[match_pattern] abbrev asPrinted : TriggerPutHow := .battlefieldEntryState false false
@[match_pattern] abbrev tapped : TriggerPutHow := .battlefieldEntryState true false
@[match_pattern] abbrev asArtifact : TriggerPutHow := .battlefieldEntryState false true
@[match_pattern] abbrev underOwner : TriggerPutHow := .battlefieldEntryState true true

end TriggerPutHow

/-- What a later step of `TriggerResolution.put` can read, or how the
card enters. -/
inductive TriggerPutNote where
  /-- Nothing (`false, false`), for attach (`true, false`), as Food (`false, true`), or entering with `mods` (`isEntering = true`). -/
  | putNoteKind (forAttach : Bool := false) (asFood : Bool := false)
      (mods : List TriggerEnterWith := []) (isEntering : Bool := false)
deriving Repr, Inhabited, BEq

namespace TriggerPutNote

@[match_pattern] abbrev putRecord (forAttach : Bool := false) (asFood : Bool := false) : TriggerPutNote :=
  .putNoteKind forAttach asFood [] false
@[match_pattern] abbrev entering (mods : List TriggerEnterWith) : TriggerPutNote :=
  .putNoteKind false false mods true
@[match_pattern] abbrev none : TriggerPutNote := .putRecord false false
@[match_pattern] abbrev forAttach : TriggerPutNote := .putRecord true false
@[match_pattern] abbrev asFood : TriggerPutNote := .putRecord false true

/-- Modifications carried by `entering`. Any other note changes nothing. -/
def enterMods : TriggerPutNote → List TriggerEnterWith
  | .entering mods => mods
  | _ => []

end TriggerPutNote

/-- How `TriggerResolution.chooseModes` chooses those modes. -/
inductive TriggerModeHow where
  /-- Unused/one/preset/fromLastKnown/numeric mode (`condOpt = none && indicesOpt = none`), or conditional (`condOpt = some cond`, CR 608.2c) / Hawkeye (`indicesOpt = some indices`) mode. -/
  | modeHowKind (alt1 : Bool := false) (alt2 : Bool := false)
      (preset : Bool := false) (fromLastKnownFlag : Bool := false)
      (count : Option Nat := none)
      (condOpt : Option ConditionSelector := none)
      (indicesOpt : Option (List Nat) := none)
deriving Repr, Inhabited, BEq

namespace TriggerModeHow

@[match_pattern] abbrev numericMode (n : Nat) (unlessPays : Bool := false) : TriggerModeHow :=
  .modeHowKind unlessPays false false false (some n) none none
@[match_pattern] abbrev conditionalMode (cond : ConditionSelector) (ifElseBranch : Bool := false) : TriggerModeHow :=
  .modeHowKind ifElseBranch false false false none (some cond) none
@[match_pattern] abbrev hawkeyeIndices (indices : List Nat) : TriggerModeHow :=
  .modeHowKind false false false false none none (some indices)
@[match_pattern] abbrev unusedOrOneMode (thisTurn : Bool := false) (lifetimeOrVision : Bool := false) : TriggerModeHow :=
  .modeHowKind thisTurn lifetimeOrVision false false none none none
@[match_pattern] abbrev presetMode (hyde : Bool := false) : TriggerModeHow :=
  .modeHowKind hyde false true false none none none
@[match_pattern] abbrev fromLastKnown : TriggerModeHow :=
  .modeHowKind false false false true none none none
@[match_pattern] abbrev one : TriggerModeHow := .unusedOrOneMode false false
@[match_pattern] abbrev oneUnusedThisTurn : TriggerModeHow := .unusedOrOneMode true false
@[match_pattern] abbrev oneUnused : TriggerModeHow := .unusedOrOneMode false true
@[match_pattern] abbrev vision : TriggerModeHow := .unusedOrOneMode true true
@[match_pattern] abbrev «if» (cond : ConditionSelector) : TriggerModeHow := .conditionalMode cond false
@[match_pattern] abbrev ifElse (cond : ConditionSelector) : TriggerModeHow := .conditionalMode cond true
@[match_pattern] abbrev alreadyChosen : TriggerModeHow := .presetMode false
@[match_pattern] abbrev plusOneOrRemoveCounter : TriggerModeHow := .presetMode true
@[match_pattern] abbrev fraTrigger (count : Nat) : TriggerModeHow := .numericMode count false
@[match_pattern] abbrev unlessPays (n : Nat) : TriggerModeHow := .numericMode n true

end TriggerModeHow

/-- What a later step of `TriggerResolution.destroy` can read. -/
abbrev TriggerDestroyNote := TriggerDamageNote

namespace TriggerDestroyNote

@[match_pattern] abbrev destroyRecord (countDestroyed : Bool := false) (forAmassOrToken : Bool := false) : TriggerDestroyNote :=
  .destroyNoteKind countDestroyed forAmassOrToken false
@[match_pattern] abbrev drawIf (legendaryEnchantment : Bool := false) : TriggerDestroyNote :=
  .destroyNoteKind legendaryEnchantment false true
@[match_pattern] abbrev destroyRider (gainLifeEach : Bool := false) : TriggerDestroyNote :=
  .destroyNoteKind gainLifeEach true true
@[match_pattern] abbrev none : TriggerDestroyNote := .destroyNoteKind false false false
@[match_pattern] abbrev countDestroyed : TriggerDestroyNote := .destroyNoteKind true false false
@[match_pattern] abbrev forAmass : TriggerDestroyNote := .destroyNoteKind false true false
@[match_pattern] abbrev chosenToken : TriggerDestroyNote := .destroyNoteKind true true false
@[match_pattern] abbrev drawIfNotAttacking : TriggerDestroyNote := .destroyNoteKind false false true
@[match_pattern] abbrev drawIfLegendaryEnchantment : TriggerDestroyNote := .destroyNoteKind true false true
@[match_pattern] abbrev controllerCreatesHuman : TriggerDestroyNote := .destroyNoteKind false true true
@[match_pattern] abbrev gainLifeEach : TriggerDestroyNote := .destroyNoteKind true true true

end TriggerDestroyNote

/-- How `TriggerResolution.fight` uses that creature. -/
inductive TriggerFightHow where
  /-- Mutual fight (`false, false, none`), reflexive power damage (`true, false, none`), fight up to one other (`false, true, none`), or deal `k` times its power (`timesPower = some k`). -/
  | fightHowKind (reflexive : Bool := false) (upToOneOther : Bool := false)
      (timesPower : Option Nat := none)
deriving Repr, Inhabited, BEq

namespace TriggerFightHow

@[match_pattern] abbrev «mutual» : TriggerFightHow := .fightHowKind false false none
@[match_pattern] abbrev reflexive : TriggerFightHow := .fightHowKind true false none
@[match_pattern] abbrev upToOneOther : TriggerFightHow := .fightHowKind false true none
@[match_pattern] abbrev timesPower (k : Nat) : TriggerFightHow := .fightHowKind false false (some k)

end TriggerFightHow

/-- How long `TriggerResolution.gainControl` lasts. -/
abbrev TriggerControlHow := TriggerDamageNote

namespace TriggerControlHow

@[match_pattern] abbrev controlDuration (whileSource : Bool := false) (nextTurnOrVillain : Bool := false) : TriggerControlHow :=
  .controlHowKind whileSource nextTurnOrVillain false
@[match_pattern] abbrev multiControl (exchange : Bool := false) : TriggerControlHow :=
  .controlHowKind exchange false true
@[match_pattern] abbrev untilEndOfTurn : TriggerControlHow := .controlDuration false false
@[match_pattern] abbrev whileSourceRemains : TriggerControlHow := .controlDuration true false
@[match_pattern] abbrev duringNextTurn : TriggerControlHow := .controlDuration false true
@[match_pattern] abbrev untilEotOrNextIfVillain : TriggerControlHow := .controlDuration true true
@[match_pattern] abbrev oppArtifacts : TriggerControlHow := .multiControl false
@[match_pattern] abbrev exchangeTargets : TriggerControlHow := .multiControl true

end TriggerControlHow

/-- What `TriggerResolution.cant` prevents, and who can't do it.
The announced permanent can't be blocked this turn is `.beBlocked`.
The source is `.beBlocked .source`.
The enchanted creature is `.beBlocked .enchanted`.
The target, while the source remains, is `.beBlocked (.target .whileSource)`.
Can't be blocked this turn except by creatures with haste is
`.beBlockedExceptByHaste`.
The announced permanent can't become untapped for as long as you control
the source is `.untapWhileYouControl`. An opponent's creature is the only
recipient. -/
inductive ActionSelector where
  /-- Combat blocking restriction (`!stateOrSpell`) or untap/spell-cast/counter/attack restriction (`stateOrSpell`) on `who`. -/
  | actionRestrictionKind (who : ObjectSelector := .target)
      (alt1 : Bool := false) (alt2 : Bool := false) (stateOrSpell : Bool := false)
deriving Repr, Inhabited, BEq

namespace ActionSelector

@[match_pattern] abbrev combatRestriction (who : ObjectSelector := .target) (exceptHaste : Bool := false) (canBlockOrMostLife : Bool := false) : ActionSelector :=
  .actionRestrictionKind who exceptHaste canBlockOrMostLife false
@[match_pattern] abbrev stateOrSpellRestriction (who : ObjectSelector := .target) (castSpells : Bool := false) (beCounteredOrAttackJaces : Bool := false) : ActionSelector :=
  .actionRestrictionKind who castSpells beCounteredOrAttackJaces true
@[match_pattern] abbrev beBlocked (who : ObjectSelector := .target) : ActionSelector := .combatRestriction who false false
@[match_pattern] abbrev beBlockedExceptByHaste (who : ObjectSelector := .target) : ActionSelector := .combatRestriction who true false
@[match_pattern] abbrev block (who : ObjectSelector := .target) : ActionSelector := .combatRestriction who false true
@[match_pattern] abbrev beBlockedByMostLifePlayer (who : ObjectSelector := .target) : ActionSelector := .combatRestriction who true true
@[match_pattern] abbrev untapWhileYouControl (who : ObjectSelector := .target) : ActionSelector := .stateOrSpellRestriction who false false
@[match_pattern] abbrev castSpellsThisTurn (who : ObjectSelector := .any) : ActionSelector := .stateOrSpellRestriction who true false
@[match_pattern] abbrev beCountered (who : ObjectSelector := .target) : ActionSelector := .stateOrSpellRestriction who false true
@[match_pattern] abbrev attackJaces (who : ObjectSelector := .opponentsCreatures) : ActionSelector := .stateOrSpellRestriction who true true

end ActionSelector

/-- Layer 4 type-changing and animation grants (CR 613.1d). -/
inductive Layer4TypeGrant where
  /-- Additional type / subtype / animate source land (`!isPtCreature`), or become a creature with base P/T and keywords (`isPtCreature = true`). -/
  | layer4TypeKind (artifactCreature : Bool := false) (flag : Bool := false)
      (subtype : Option String := none) (power toughness : Nat := 0)
      (flying : Bool := false) (firstStrike : Bool := false) (isAnimateLand : Bool := false)
      (p : Int := 4) (t : Int := 4) (kwOpt : Option String := none)
      (typesOpt : Option (Array String) := none) (kOpt : Option Keywords := none)
      (isPtCreature : Bool := false)
deriving Repr, Inhabited, BEq

namespace Layer4TypeGrant

@[match_pattern] abbrev typeSubtypeOrAnimateLand (artifactCreature : Bool := false) (flag : Bool := false)
    (subtype : Option String := none) (power toughness : Nat := 0)
    (flying : Bool := false) (firstStrike : Bool := false) (isAnimateLand : Bool := false) : Layer4TypeGrant :=
  .layer4TypeKind artifactCreature flag subtype power toughness flying firstStrike isAnimateLand 4 4 none none none false
@[match_pattern] abbrev typeOrArtifactCreature (artifactCreature : Bool := false) (flag : Bool := false) : Layer4TypeGrant :=
  .typeSubtypeOrAnimateLand artifactCreature flag none 0 0 false false false
@[match_pattern] abbrev subtypeWithLandsPT (subtype : String) : Layer4TypeGrant :=
  .typeSubtypeOrAnimateLand false false (some subtype) 0 0 false false false
@[match_pattern] abbrev animateLand (power toughness : Nat) (flying firstStrike : Bool) : Layer4TypeGrant :=
  .typeSubtypeOrAnimateLand false false none power toughness flying firstStrike true
@[match_pattern] abbrev artifactCreature (p : Int := 4) (t : Int := 4) (kw : String := "flying") : Layer4TypeGrant :=
  .layer4TypeKind false false none 0 0 false false false p t (some kw) none none true
@[match_pattern] abbrev typesPTAndKeywords (types : Array String) (power toughness : Int) (k : Keywords) : Layer4TypeGrant :=
  .layer4TypeKind false false none 0 0 false false false power toughness none (some types) (some k) true
@[match_pattern] abbrev artifact : Layer4TypeGrant := .typeOrArtifactCreature false false
@[match_pattern] abbrev bearType : Layer4TypeGrant := .typeOrArtifactCreature false true
@[match_pattern] abbrev constructHero : Layer4TypeGrant := .typeOrArtifactCreature true false
@[match_pattern] abbrev artifactCreatureVehicle : Layer4TypeGrant := .typeOrArtifactCreature true true

end Layer4TypeGrant

/-- Layer 6 ability-adding, keyword, ability-removing, and restriction grants (CR 613.1f). -/
inductive Layer6AbilityGrant where
  /-- Granted/lost ability (`kOpt = none && optionsOpt = none && cantOpt = none`), keywords (`kOpt = some k`), choice (`optionsOpt = some options`), or prevent `action` (`cantOpt = some action`, CR 613.1f). -/
  | layer6AbilityKind (alt1 : Bool := false) (alt2 : Bool := false) (combatOrCast : Bool := false)
      (lost : Option AbilitySelector := none)
      (kOpt : Option Keywords := none) (optionsOpt : Option (List Nat) := none)
      (cantOpt : Option ActionSelector := none)
deriving Repr, Inhabited, BEq

namespace Layer6AbilityGrant

@[match_pattern] abbrev grantedOrLostAbility (alt1 : Bool := false) (alt2 : Bool := false) (combatOrCast : Bool := false)
    (lost : Option AbilitySelector := none) : Layer6AbilityGrant :=
  .layer6AbilityKind alt1 alt2 combatOrCast lost none none none
@[match_pattern] abbrev cant (action : ActionSelector) : Layer6AbilityGrant :=
  .layer6AbilityKind false false false none none none (some action)
@[match_pattern] abbrev grantedAbilityOrTrigger (alt1 : Bool := false) (alt2 : Bool := false) (combatOrCast : Bool := false) : Layer6AbilityGrant :=
  .grantedOrLostAbility alt1 alt2 combatOrCast none
@[match_pattern] abbrev lose (what : AbilitySelector) : Layer6AbilityGrant :=
  .grantedOrLostAbility false false false (some what)
@[match_pattern] abbrev keywords (k : Keywords) : Layer6AbilityGrant :=
  .layer6AbilityKind false false false none (some k) none none
@[match_pattern] abbrev choiceOfKeywords (options : List Nat) : Layer6AbilityGrant :=
  .layer6AbilityKind false false false none none (some options) none
@[match_pattern] abbrev grantedProtectionOrAbility (hexproof : Bool := false) (landfallOrIronFist : Bool := false) : Layer6AbilityGrant :=
  .grantedAbilityOrTrigger hexproof landfallOrIronFist false
@[match_pattern] abbrev combatDamageTrigger (drawTwo : Bool := false) : Layer6AbilityGrant :=
  .grantedAbilityOrTrigger drawTwo false true
@[match_pattern] abbrev castOrGraveyardAbility (emrakul : Bool := false) : Layer6AbilityGrant :=
  .grantedAbilityOrTrigger emrakul true true
@[match_pattern] abbrev protectionEverything : Layer6AbilityGrant := .grantedAbilityOrTrigger false false false
@[match_pattern] abbrev hexproofWhileSource : Layer6AbilityGrant := .grantedAbilityOrTrigger true false false
@[match_pattern] abbrev landfallCreateElf : Layer6AbilityGrant := .grantedAbilityOrTrigger false true false
@[match_pattern] abbrev ironFistTap : Layer6AbilityGrant := .grantedAbilityOrTrigger true true false
@[match_pattern] abbrev flashback : Layer6AbilityGrant := .grantedAbilityOrTrigger false true true
@[match_pattern] abbrev emrakulManaAndCast : Layer6AbilityGrant := .grantedAbilityOrTrigger true true true

end Layer6AbilityGrant

/-- Layer 7 power/toughness and combat damage assignment grants (CR 613.1g / CR 510.1c). -/
inductive Layer7PtGrant where
  /-- Set base P/T to `power`/`toughness` (`powerOpt = some power, toughnessOpt = some toughness`, CR 613.4b Layer 7b), or base power equal hand / assign combat damage equal toughness (`powerOpt = none`). -/
  | layer7PtKind (powerOpt : Option NumberSelector := none) (toughnessOpt : Option NumberSelector := none)
      (assignToughness : Bool := false)
deriving Repr, Inhabited, BEq

namespace Layer7PtGrant

@[match_pattern] abbrev basePT (power toughness : NumberSelector) : Layer7PtGrant :=
  .layer7PtKind (some power) (some toughness) false
@[match_pattern] abbrev dynamicOrToughnessGrant (assignToughness : Bool := false) : Layer7PtGrant :=
  .layer7PtKind none none assignToughness
@[match_pattern] abbrev basePowerEqualHand : Layer7PtGrant := .dynamicOrToughnessGrant false
@[match_pattern] abbrev assignCombatDamageEqualToughness : Layer7PtGrant := .dynamicOrToughnessGrant true

end Layer7PtGrant

/-- Replacement, prevention, permission, cost-reduction, turn, and emblem grants (CR 614 / CR 615 / CR 114). -/
inductive RuleEffectGrant where
  /-- Replacement/turn/emblem/win rule (`costLess = none, emblemDamage = none`), spells of `which` cost `n` less (`costLess = some which`), or emblem cast-spell damage `d` (`emblemDamage = some d`). -/
  | ruleEffectKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (cat1 : Bool := false) (cat2 : Bool := false)
      (costLess : Option SpellCostLess := none) (nOpt : Option NumberSelector := none)
      (emblemDamage : Option Nat := none)
deriving Repr, Inhabited, BEq

namespace RuleEffectGrant

@[match_pattern] abbrev spellsCostLess (which : SpellCostLess) (n : NumberSelector) : RuleEffectGrant :=
  .ruleEffectKind false false false false false (some which) (some n) none
@[match_pattern] abbrev emblemCastSpellDamage (d : Nat) : RuleEffectGrant :=
  .ruleEffectKind false false false false false none none (some d)
@[match_pattern] abbrev replacementOrTurnRule (alt1 : Bool := false) (alt2 : Bool := false) (turnOrPhase : Bool := false) : RuleEffectGrant :=
  .ruleEffectKind alt1 alt2 turnOrPhase false false none none none
@[match_pattern] abbrev emblemOrTeferiRule (teferi : Bool := false) : RuleEffectGrant :=
  .ruleEffectKind teferi false false true false none none none
@[match_pattern] abbrev emblemOrSpellCopy (nextSpellCopy : Bool := false) (flag : Bool := false) : RuleEffectGrant :=
  .ruleEffectKind nextSpellCopy flag false false true none none none
@[match_pattern] abbrev winTheGame : RuleEffectGrant :=
  .ruleEffectKind false false false true true none none none
@[match_pattern] abbrev replacementOrPermissionRule (preventDamage : Bool := false) (playNotedOrJace : Bool := false) : RuleEffectGrant :=
  .replacementOrTurnRule preventDamage playNotedOrJace false
@[match_pattern] abbrev turnOrPhaseRule (extraLand : Bool := false) (extraTurnOrCombat : Bool := false) : RuleEffectGrant :=
  .replacementOrTurnRule extraLand extraTurnOrCombat true
@[match_pattern] abbrev replace : RuleEffectGrant := .replacementOrTurnRule false false false
@[match_pattern] abbrev preventDamageWhileSource : RuleEffectGrant := .replacementOrTurnRule true false false
@[match_pattern] abbrev playNotedUntilNextTurn : RuleEffectGrant := .replacementOrTurnRule false true false
@[match_pattern] abbrev jaceLoyaltyAtInstantSpeed : RuleEffectGrant := .replacementOrTurnRule true true false
@[match_pattern] abbrev mountainsAddExtraRed : RuleEffectGrant := .replacementOrTurnRule false false true
@[match_pattern] abbrev extraLand : RuleEffectGrant := .replacementOrTurnRule true false true
@[match_pattern] abbrev extraTurn : RuleEffectGrant := .replacementOrTurnRule false true true
@[match_pattern] abbrev additionalCombatPhase : RuleEffectGrant := .replacementOrTurnRule true true true
@[match_pattern] abbrev emblemDrawOnCast : RuleEffectGrant := .emblemOrTeferiRule false
@[match_pattern] abbrev teferisReproach : RuleEffectGrant := .emblemOrTeferiRule true
@[match_pattern] abbrev emblemCreaturesGetTwoTwo (flying : Bool := false) : RuleEffectGrant := .emblemOrSpellCopy false flying
@[match_pattern] abbrev nextSpellCopy (mvAtMostSourcePower : Bool := false) : RuleEffectGrant := .emblemOrSpellCopy true mvAtMostSourcePower

end RuleEffectGrant

/-- One-shot keyword actions and permanent state changes (CR 701 / CR 702 / CR 724). -/
inductive ActionStateGrant where
  /-- Permanent/target/keyword/numeric action (`empowerOpt = none && fightHow = none && recruitOpt = none && hostOpt = none`), empower/fight (`empowerOpt = some n` or `fightHow = some how`), or recruit/attach (`recruitOpt = some who` or `hostOpt = some host`). -/
  | actionStateKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false) (alt4 : Bool := false)
      (keywordOrSpecial : Bool := false) (natN : Option Nat := none) (paid : Nat := 0)
      (empowerOpt : Option NumberSelector := none) (fightHow : Option TriggerFightHow := none)
      (recruitOpt : Option PlayerSelector := none) (hostOpt : Option ObjectSelector := none)
deriving Repr, Inhabited, BEq

namespace ActionStateGrant

@[match_pattern] abbrev natActionState (n : Nat) (paid : Nat := 0) (reflexive : Bool := false) : ActionStateGrant :=
  .actionStateKind reflexive false false false false (some n) paid none none none none
@[match_pattern] abbrev empowerJace (n : NumberSelector) : ActionStateGrant :=
  .actionStateKind false false false false false none 0 (some n) none none none
@[match_pattern] abbrev fight (how : TriggerFightHow := .mutual) : ActionStateGrant :=
  .actionStateKind false false false false false none 0 none (some how) none none
@[match_pattern] abbrev recruit (who : PlayerSelector := .recruit) : ActionStateGrant :=
  .actionStateKind false false false false false none 0 none none (some who) none
@[match_pattern] abbrev attachTo (host : ObjectSelector) : ActionStateGrant :=
  .actionStateKind false false false false false none 0 none none none (some host)
@[match_pattern] abbrev permanentOrTargetAction (alt1 : Bool := false) (alt2 : Bool := false) (targetOrToken : Bool := false) : ActionStateGrant :=
  .actionStateKind alt1 alt2 targetOrToken false false none 0 none none none none
@[match_pattern] abbrev keywordOrSpecialAction (alt1 : Bool := false) (alt2 : Bool := false) (special : Bool := false) (counterSpell : Bool := false) : ActionStateGrant :=
  .actionStateKind alt1 alt2 special counterSpell true none 0 none none none none
@[match_pattern] abbrev permanentStateChange (transformed : Bool := false) (harnessedOrFaceUp : Bool := false) : ActionStateGrant :=
  .permanentOrTargetAction transformed harnessedOrFaceUp false
@[match_pattern] abbrev attacking : ActionStateGrant := .permanentOrTargetAction false false false
@[match_pattern] abbrev transformed : ActionStateGrant := .permanentOrTargetAction true false false
@[match_pattern] abbrev harnessed : ActionStateGrant := .permanentOrTargetAction false true false
@[match_pattern] abbrev faceUp : ActionStateGrant := .permanentOrTargetAction true true false
@[match_pattern] abbrev targetOrTokenAction (arwenShare : Bool := false) (phaseOutOrIncubator : Bool := false) : ActionStateGrant :=
  .permanentOrTargetAction arwenShare phaseOutOrIncubator true
@[match_pattern] abbrev newTargets : ActionStateGrant := .permanentOrTargetAction false false true
@[match_pattern] abbrev arwenShare : ActionStateGrant := .permanentOrTargetAction true false true
@[match_pattern] abbrev phaseOutKicker : ActionStateGrant := .permanentOrTargetAction false true true
@[match_pattern] abbrev transformedIncubator : ActionStateGrant := .permanentOrTargetAction true true true
@[match_pattern] abbrev keywordAction (explored : Bool := false) (investigateOrConnive : Bool := false) : ActionStateGrant :=
  .keywordOrSpecialAction explored investigateOrConnive false false
@[match_pattern] abbrev monarch : ActionStateGrant := .keywordOrSpecialAction false false false false
@[match_pattern] abbrev explored : ActionStateGrant := .keywordOrSpecialAction true false false false
@[match_pattern] abbrev investigate : ActionStateGrant := .keywordOrSpecialAction false true false false
@[match_pattern] abbrev connive : ActionStateGrant := .keywordOrSpecialAction true true false false
@[match_pattern] abbrev prepared (prepared : Bool := true) : ActionStateGrant :=
  .keywordOrSpecialAction prepared false true false
@[match_pattern] abbrev cascadeOrRing (ringTempts : Bool := false) : ActionStateGrant :=
  .keywordOrSpecialAction ringTempts true true false
@[match_pattern] abbrev cascade : ActionStateGrant := .keywordOrSpecialAction false true true false
@[match_pattern] abbrev ringTempts : ActionStateGrant := .keywordOrSpecialAction true true true false
@[match_pattern] abbrev counterSpell : ActionStateGrant := .keywordOrSpecialAction false false false true
@[match_pattern] abbrev noteResolveThisTurn (limit : Nat) : ActionStateGrant := .natActionState limit 0 false
@[match_pattern] abbrev mshReflexive (kind paid : Nat) : ActionStateGrant := .natActionState kind paid true

end ActionStateGrant

/-- What `TriggerResolution.grant` grants, organized by CR 613 layers, CR 614/615 rule effects, and CR 701 actions. -/
inductive TriggerGrantWhat where
  /-- Unified grant selector: Layer 6 (`layer6Opt = some g`), Layer 1 (`copyOpt = some of`), Layer 2 (`controlHow = some how`), Layer 4 (`layer4 = some g`), Layer 7 (`ptOpt = some g`), Rule (`ruleOpt = some g`), or ActionState (`actionStateOpt = some g`). -/
  | triggerGrantKind (layer6Opt : Option Layer6AbilityGrant := none)
      (copyOpt : Option ObjectSelector := none) (controlHow : Option TriggerControlHow := none)
      (layer4 : Option Layer4TypeGrant := none)
      (ptOpt : Option Layer7PtGrant := none) (ruleOpt : Option RuleEffectGrant := none)
      (actionStateOpt : Option ActionStateGrant := none)
deriving Repr, Inhabited, BEq

namespace TriggerGrantWhat

@[match_pattern] abbrev layer6Ability (g : Layer6AbilityGrant) : TriggerGrantWhat :=
  .triggerGrantKind (some g) none none none none none none
@[match_pattern] abbrev actionState (g : ActionStateGrant) : TriggerGrantWhat :=
  .triggerGrantKind none none none none none none (some g)
@[match_pattern] abbrev copy (of : ObjectSelector) : TriggerGrantWhat :=
  .triggerGrantKind none (some of) none none none none none
@[match_pattern] abbrev control (how : TriggerControlHow) : TriggerGrantWhat :=
  .triggerGrantKind none none (some how) none none none none
@[match_pattern] abbrev layer4Type (g : Layer4TypeGrant) : TriggerGrantWhat :=
  .triggerGrantKind none none none (some g) none none none
@[match_pattern] abbrev layer7PT (g : Layer7PtGrant) : TriggerGrantWhat :=
  .triggerGrantKind none none none none (some g) none none
@[match_pattern] abbrev ruleEffect (g : RuleEffectGrant) : TriggerGrantWhat :=
  .triggerGrantKind none none none none none (some g) none

-- Layer4TypeGrant aliases
@[match_pattern] abbrev artifact : TriggerGrantWhat := .layer4Type .artifact
@[match_pattern] abbrev bearType : TriggerGrantWhat := .layer4Type .bearType
@[match_pattern] abbrev constructHero : TriggerGrantWhat := .layer4Type .constructHero
@[match_pattern] abbrev artifactCreatureVehicle : TriggerGrantWhat := .layer4Type .artifactCreatureVehicle
@[match_pattern] abbrev artifactCreature (p : Int := 4) (t : Int := 4) (kw : String := "flying") : TriggerGrantWhat :=
  .layer4Type (.artifactCreature p t kw)
@[match_pattern] abbrev subtypeWithLandsPT (subtype : String) : TriggerGrantWhat := .layer4Type (.subtypeWithLandsPT subtype)
@[match_pattern] abbrev typesPTAndKeywords (types : Array String) (power toughness : Int) (k : Keywords) : TriggerGrantWhat :=
  .layer4Type (.typesPTAndKeywords types power toughness k)
@[match_pattern] abbrev animateLand (power toughness : Nat) (flying firstStrike : Bool) : TriggerGrantWhat :=
  .layer4Type (.animateLand power toughness flying firstStrike)

-- Layer6AbilityGrant aliases
@[match_pattern] abbrev protectionEverything : TriggerGrantWhat := .layer6Ability .protectionEverything
@[match_pattern] abbrev keywords (k : Keywords) : TriggerGrantWhat := .layer6Ability (.keywords k)
def doubleStrike : TriggerGrantWhat := .keywords Keyword.doubleStrike
@[match_pattern] abbrev hexproofWhileSource : TriggerGrantWhat := .layer6Ability .hexproofWhileSource
@[match_pattern] abbrev choiceOfKeywords (options : List Nat) : TriggerGrantWhat := .layer6Ability (.choiceOfKeywords options)
@[match_pattern] abbrev landfallCreateElf : TriggerGrantWhat := .layer6Ability .landfallCreateElf
@[match_pattern] abbrev ironFistTap : TriggerGrantWhat := .layer6Ability .ironFistTap
@[match_pattern] abbrev combatDamageCreateTreasure : TriggerGrantWhat := .layer6Ability (.combatDamageTrigger false)
@[match_pattern] abbrev combatDamageDrawTwo : TriggerGrantWhat := .layer6Ability (.combatDamageTrigger true)
@[match_pattern] abbrev flashback : TriggerGrantWhat := .layer6Ability .flashback
@[match_pattern] abbrev emrakulManaAndCast : TriggerGrantWhat := .layer6Ability .emrakulManaAndCast
@[match_pattern] abbrev lose (what : AbilitySelector) : TriggerGrantWhat := .layer6Ability (.lose what)
@[match_pattern] abbrev cant (action : ActionSelector) : TriggerGrantWhat := .layer6Ability (.cant action)

-- Layer7PtGrant aliases
@[match_pattern] abbrev basePT (power toughness : NumberSelector) : TriggerGrantWhat := .layer7PT (.basePT power toughness)
@[match_pattern] abbrev basePowerEqualHand : TriggerGrantWhat := .layer7PT .basePowerEqualHand
@[match_pattern] abbrev assignCombatDamageEqualToughness : TriggerGrantWhat := .layer7PT .assignCombatDamageEqualToughness

-- RuleEffectGrant aliases
@[match_pattern] abbrev replace : TriggerGrantWhat := .ruleEffect .replace
@[match_pattern] abbrev preventDamageWhileSource : TriggerGrantWhat := .ruleEffect .preventDamageWhileSource
@[match_pattern] abbrev spellsCostLess (which : SpellCostLess) (n : NumberSelector) : TriggerGrantWhat := .ruleEffect (.spellsCostLess which n)
@[match_pattern] abbrev playNotedUntilNextTurn : TriggerGrantWhat := .ruleEffect .playNotedUntilNextTurn
@[match_pattern] abbrev jaceLoyaltyAtInstantSpeed : TriggerGrantWhat := .ruleEffect .jaceLoyaltyAtInstantSpeed
@[match_pattern] abbrev mountainsAddExtraRed : TriggerGrantWhat := .ruleEffect .mountainsAddExtraRed
@[match_pattern] abbrev emblemCastSpellDamage (n : Nat) : TriggerGrantWhat := .ruleEffect (.emblemCastSpellDamage n)
@[match_pattern] abbrev emblemDrawOnCast : TriggerGrantWhat := .ruleEffect .emblemDrawOnCast
@[match_pattern] abbrev emblemCreaturesGetTwoTwo : TriggerGrantWhat := .ruleEffect (.emblemCreaturesGetTwoTwo false)
@[match_pattern] abbrev emblemCreaturesGetTwoTwoFlying : TriggerGrantWhat := .ruleEffect (.emblemCreaturesGetTwoTwo true)
@[match_pattern] abbrev nextSpellCopy (mvAtMostSourcePower : Bool := false) : TriggerGrantWhat := .ruleEffect (.nextSpellCopy mvAtMostSourcePower)
@[match_pattern] abbrev extraLand : TriggerGrantWhat := .ruleEffect .extraLand
@[match_pattern] abbrev extraTurn : TriggerGrantWhat := .ruleEffect .extraTurn
@[match_pattern] abbrev teferisReproach : TriggerGrantWhat := .ruleEffect .teferisReproach
@[match_pattern] abbrev additionalCombatPhase : TriggerGrantWhat := .ruleEffect .additionalCombatPhase
@[match_pattern] abbrev winTheGame : TriggerGrantWhat := .ruleEffect .winTheGame

-- ActionStateGrant aliases
@[match_pattern] abbrev attacking : TriggerGrantWhat := .actionState .attacking
@[match_pattern] abbrev newTargets : TriggerGrantWhat := .actionState .newTargets
@[match_pattern] abbrev transformed : TriggerGrantWhat := .actionState .transformed
@[match_pattern] abbrev harnessed : TriggerGrantWhat := .actionState .harnessed
@[match_pattern] abbrev arwenShare : TriggerGrantWhat := .actionState .arwenShare
@[match_pattern] abbrev phaseOutKicker : TriggerGrantWhat := .actionState .phaseOutKicker
@[match_pattern] abbrev monarch : TriggerGrantWhat := .actionState .monarch
@[match_pattern] abbrev explored : TriggerGrantWhat := .actionState .explored
@[match_pattern] abbrev transformedIncubator : TriggerGrantWhat := .actionState .transformedIncubator
@[match_pattern] abbrev faceUp : TriggerGrantWhat := .actionState .faceUp
@[match_pattern] abbrev prepared (prepared : Bool := true) : TriggerGrantWhat := .actionState (.prepared prepared)
@[match_pattern] abbrev investigate : TriggerGrantWhat := .actionState .investigate
@[match_pattern] abbrev empowerJace (n : NumberSelector) : TriggerGrantWhat := .actionState (.empowerJace n)
@[match_pattern] abbrev recruit (who : PlayerSelector := .recruit) : TriggerGrantWhat := .actionState (.recruit who)
@[match_pattern] abbrev noteResolveThisTurn (limit : Nat) : TriggerGrantWhat := .actionState (.noteResolveThisTurn limit)
@[match_pattern] abbrev mshReflexive (kind paid : Nat) : TriggerGrantWhat := .actionState (.mshReflexive kind paid)
@[match_pattern] abbrev connive : TriggerGrantWhat := .actionState .connive
@[match_pattern] abbrev fight (how : TriggerFightHow := .mutual) : TriggerGrantWhat := .actionState (.fight how)
@[match_pattern] abbrev attachTo (host : ObjectSelector) : TriggerGrantWhat := .actionState (.attachTo host)
@[match_pattern] abbrev cascade : TriggerGrantWhat := .actionState .cascade
@[match_pattern] abbrev ringTempts : TriggerGrantWhat := .actionState .ringTempts
@[match_pattern] abbrev counterSpell : TriggerGrantWhat := .actionState .counterSpell

end TriggerGrantWhat


/-- What a later step of `TriggerResolution.mill` can read. -/
inductive TriggerMillNote where
  /-- Mill record (`toHand = none, life = none, subtype = none`), put milled cards into hand (`toHand = some which`), permanent and gain life (`life = some n`), or subtype/enchantment to hand (`subtype = some s`). -/
  | millNoteKind (milledCards : Bool := false) (opponentsOrFreeCast : Bool := false)
      (toHand : Option MilledToHand := Option.none) (life : Option Nat := Option.none)
      (subtype : Option String := Option.none)
deriving Repr, Inhabited, BEq

namespace TriggerMillNote

@[match_pattern] abbrev millRecord (milledCards : Bool := false) (opponentsOrFreeCast : Bool := false) : TriggerMillNote :=
  .millNoteKind milledCards opponentsOrFreeCast Option.none Option.none Option.none
@[match_pattern] abbrev toHand (which : MilledToHand) : TriggerMillNote :=
  .millNoteKind false false (some which) Option.none Option.none
@[match_pattern] abbrev permanentAndGainLife (life : Nat) : TriggerMillNote :=
  .millNoteKind false false Option.none (some life) Option.none
@[match_pattern] abbrev subtypeOrEnchantmentToHand (subtype : String) : TriggerMillNote :=
  .millNoteKind false false Option.none Option.none (some subtype)
@[match_pattern] abbrev none : TriggerMillNote := .millRecord false false
@[match_pattern] abbrev milledCards : TriggerMillNote := .millRecord true false
@[match_pattern] abbrev opponentsMilled : TriggerMillNote := .millRecord false true
@[match_pattern] abbrev freeCastFromGraveyard : TriggerMillNote := .millRecord true true

end TriggerMillNote

/-- How many cards `TriggerResolution.revealFromHand` shows (CR 701.16). -/
abbrev TriggerRevealCount := AbilitySelector

namespace TriggerRevealCount

@[match_pattern] abbrev hand : TriggerRevealCount := .revealCountKind false
@[match_pattern] abbrev onePlusCreatureCards : TriggerRevealCount := .revealCountKind true

end TriggerRevealCount

/-- How far `TriggerResolution.revealLibrary` looks from the top of a library. -/
inductive TriggerLibraryHow where
  /-- Top `n` (`topN = some n`), `topNumber` (`topNum = some num`), reveal from hand (`fromHand = some count`, CR 701.16), or reveal until / search (`topN = none && topNum = none && fromHand = none`). -/
  | libraryHowKind (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (searchOrSpecialFlag : Bool := false) (fromHand : Option TriggerRevealCount := none)
      (topN : Option Nat := none) (topNum : Option NumberSelector := none)
deriving Repr, Inhabited, BEq

namespace TriggerLibraryHow

@[match_pattern] abbrev top (n : Nat) : TriggerLibraryHow :=
  .libraryHowKind false false false false none (some n) none
@[match_pattern] abbrev topNumber (n : NumberSelector) : TriggerLibraryHow :=
  .libraryHowKind false false false false none none (some n)
@[match_pattern] abbrev fromHand (count : TriggerRevealCount) : TriggerLibraryHow :=
  .libraryHowKind false false false false (some count) none none
@[match_pattern] abbrev untilCard (saga : Bool := false) (instantOrSorcery : Bool := false) (nonland : Bool := false) : TriggerLibraryHow :=
  .libraryHowKind saga instantOrSorcery nonland false none none none
@[match_pattern] abbrev searchOrSpecial (firstResolve : Bool := false) (untilSpecial : Bool := false) (historic : Bool := false) : TriggerLibraryHow :=
  .libraryHowKind firstResolve untilSpecial historic true none none none
@[match_pattern] abbrev untilCreature : TriggerLibraryHow := .untilCard false false false
@[match_pattern] abbrev untilSaga : TriggerLibraryHow := .untilCard true false false
@[match_pattern] abbrev untilInstantOrSorcery : TriggerLibraryHow := .untilCard false true false
@[match_pattern] abbrev untilNonland : TriggerLibraryHow := .untilCard false false true
@[match_pattern] abbrev search : TriggerLibraryHow := .searchOrSpecial false false false
@[match_pattern] abbrev firstResolveUntilCreature : TriggerLibraryHow := .searchOrSpecial true false false
@[match_pattern] abbrev untilCreaturesPerOpponent : TriggerLibraryHow := .searchOrSpecial false true false
@[match_pattern] abbrev untilHistoric : TriggerLibraryHow := .searchOrSpecial false true true

end TriggerLibraryHow

/-- Where `TriggerResolution.putOnLibrary` puts the card. -/
inductive TriggerLibraryPlace where
  /-- Top/bottom placement (`!special, drawN = none`), shuffled/special placement (`special, drawN = none`), or draw `drawN` then put `putN` on top (`drawN = some d`). -/
  | libraryPlaceKind (alt1 : Bool := false) (alt2 : Bool := false) (special : Bool := false)
      (drawN : Option Nat := none) (putN : Nat := 0)
deriving Repr, Inhabited, BEq

namespace TriggerLibraryPlace

@[match_pattern] abbrev topAfterDraw (drawN putN : Nat) : TriggerLibraryPlace :=
  .libraryPlaceKind false false false (some drawN) putN
@[match_pattern] abbrev topOrBottomPlace (ownerChoice : Bool := false) (flag : Bool := false) : TriggerLibraryPlace :=
  .libraryPlaceKind ownerChoice flag false none 0
@[match_pattern] abbrev specialLibraryPlace (secondConnive : Bool := false) (revealCreatureOrAfterDraw2 : Bool := false) : TriggerLibraryPlace :=
  .libraryPlaceKind secondConnive revealCreatureOrAfterDraw2 true none 0
@[match_pattern] abbrev top : TriggerLibraryPlace := .topOrBottomPlace false false
@[match_pattern] abbrev bottom : TriggerLibraryPlace := .topOrBottomPlace false true
@[match_pattern] abbrev topOrBottom (damage2 : Bool := false) : TriggerLibraryPlace := .topOrBottomPlace true damage2
@[match_pattern] abbrev topOrBottomDamage2 : TriggerLibraryPlace := .topOrBottomPlace true true
@[match_pattern] abbrev shuffled : TriggerLibraryPlace := .specialLibraryPlace false false
@[match_pattern] abbrev secondOrBottomThenConnive : TriggerLibraryPlace := .specialLibraryPlace true false
@[match_pattern] abbrev bottomRevealCreature : TriggerLibraryPlace := .specialLibraryPlace false true
@[match_pattern] abbrev bottomAfterDrawTwo : TriggerLibraryPlace := .specialLibraryPlace true true

end TriggerLibraryPlace

/-- What a later step of `TriggerResolution.surveil` can read or do. -/
abbrev TriggerSurveilNote := AbilityCastKind

namespace TriggerSurveilNote

@[match_pattern] abbrev none : TriggerSurveilNote := .surveilRecord false false
@[match_pattern] abbrev armReturnLifeGained : TriggerSurveilNote := .surveilRecord true false
@[match_pattern] abbrev returnNoncreatureNonland : TriggerSurveilNote := .surveilRecord false true
@[match_pattern] abbrev eyeOfJace : TriggerSurveilNote := .surveilRecord true true

end TriggerSurveilNote

/-- Which outcome of `TriggerResolution.may` resolves `follow`. -/
abbrev TriggerMayWhen := AbilitySelector

namespace TriggerMayWhen

@[match_pattern] abbrev ifYouDo : TriggerMayWhen := .mayWhenKind false
@[match_pattern] abbrev ifYouDont : TriggerMayWhen := .mayWhenKind true

end TriggerMayWhen

end TriggeredAbility

export TriggeredAbility (
  ObjectSelector
  PlayerSelector
  NumberSelector
  CostSelector
  ConditionSelector
  CostReduction
  ActionSelector
)

open TriggeredAbility

/-- What a triggered ability does when it resolves (CR 608). Grouped so
`Game.applyTriggeredAbility` matches resolution shapes instead of every
constructor: scry, drawing, discarding, +1/+1 on the source, divided damage,
putting counters, removing counters, until-end-of-turn pumps, creating tokens,
exile, sacrifice, attach, amass, casting a spell, returning cards to hand,
putting onto the battlefield, adding mana, choosing modes, destroying,
fighting, granting, gaining life, losing life, milling, revealing from
a hand, revealing from a library, searching a library, tapping,
untapping, losing, and putting on a library each cover multiple printed
abilities.
A permanent target uses its own constructor: `pump`, `putCounters`,
`destroy`, `dealDamage`, `grant`, `tap`, `untap`, `exile`, `lose`,
`cant`, `becomeArtifact`, `becomePrepared`, `setBasePT`,
and `putOnLibrary`. Losing indestructible until end of turn, and losing
all abilities while the source remains, are `lose`. What is lost, and who
loses it, are arguments. A permanent that can't be blocked this turn, and
a permanent that can't untap while you control the source, are `cant`.
What it can't do, and who can't, are one `ActionSelector`. Paying mana,
and paying by sacrificing or discarding, are `pay`. What is paid is an
argument. Setting a permanent's base power and toughness to fixed values,
and setting another creature's base power and toughness equal to this
creature's, are `setBasePT`. Each statistic is a `NumberSelector`.
Who receives the new base is an `ObjectSelector`.
Gaining life is `gainLife`. How much is a `NumberSelector`.
Losing life is `loseLife`. How much is a `NumberSelector`.
Who loses it is a `PlayerSelector`.
Putting the announced permanent
on top or on the bottom of its owner's library, and putting a card from your
hand on the bottom, are `putOnLibrary`. Where the card goes is an argument.
Which card is an `ObjectSelector`.
Untapping the announced permanent, and untapping each attacking
creature, are `untap`. Who is untapped is an `ObjectSelector`.
Removing counters is `removeCounters`. Who loses them is an `ObjectSelector`.
Destroying permanents is `destroy`. Which permanents is an `ObjectSelector`.
Tapping permanents is `tap`. Who is tapped is an `ObjectSelector`.
Granting an ability is `grant`. Who receives it is an `ObjectSelector`.
A creature fighting is `fight`. Who fights is an `ObjectSelector`.
+P/+T and trample is
a sequence of `pump` and `grant`. Becoming an artifact and gaining
indestructible is a sequence of `becomeArtifact`
and `grant`. Who becomes an artifact is an `ObjectSelector`.
Who becomes prepared is an `ObjectSelector`.
Who receives a new base power and toughness is an `ObjectSelector`.
Which card is put on a library is an `ObjectSelector`.
Which cards `exile` exiles is an `ObjectSelector`.
Which cards `put` puts onto the battlefield is an `ObjectSelector`.
Tap and a stun counter is a sequence of `tap` and
`putCounters`. The source, the enchanted creature, and a follow-up while
the source remains use those same constructors. `ofSource`, `ofEnchanted`,
and `ofTargetWhileSource` map a `PermanentAction` onto them. +P/+T on the
source is `.pump (.fixed p) (.fixed t) .source`. Tapping the creature this Aura enchants is
`.tap .enchantedWhileSource`. Granting keywords to the target while the
source remains is `.grant (.keywords k) (.target .whileSource)`.
Spell steps, trigger steps, activated-ability steps, and the former
`FraResolution` steps are constructors of this inductive. -/
inductive Resolution where
  /-- Until end of turn, permanents of `who` get +`power`/+`toughness`.
  Each statistic reads its own bonus.
  The source by the greatest power among creatures you control is
  `.pump .greatestPower (.fixed 0) .source`.
  The source +1/+1 per card looked at while scrying is
  `.pump .perLookedAt .perLookedAt .source`.
  The source +1/+1 for each other creature you control is
  `.pump .perOtherCreature .perOtherCreature .source`.
  A target creature you control +1/+1 per Plains is
  `.pump .perPlains .perPlains .target`.
  The creature that caused this +P/+T is `.pump (.fixed p) (.fixed t) .cause`.
  Other permanents of a subtype +X/+X, X = this toughness, is
  `.pump .equalSourceToughness .equalSourceToughness (.othersOfSubtype subtype)`.
  Another target creature +X/+0, X = this power, is
  `.pump .equalSourcePower (.fixed 0) .target`.
  Creatures you control +P/+T is `.pump (.fixed p) (.fixed t) .creaturesYouControl`.
  Other creatures of these subtypes +P/+T is
  `.pump (.fixed p) (.fixed t) (.intersection [.creaturesYouControl, .union (subtypes.toList.map .othersOfSubtype)])`.
  Creatures opponents control +P/+T is
  `.pump (.fixed p) (.fixed t) .opponentsCreatures`.
  The announced permanent gets +P/+T is `.pump (.fixed p) (.fixed t) .target`.
  Doubling that permanent's power and toughness is `.pump .double .double .target`.
  +P/+T and trample is
  `.sequence [.pump (.fixed p) (.fixed t) .target, .grant (.keywords Keyword.trample) .target]`.
  The trigger's last-known power to the announced player or permanent, offered
  as a may, is `.may (.dealDamage .lastKnownPower .target) (.sequence []) .ifYouDo`. -/
  | combatCountersOrTokens (grantOpt : Option TriggerGrantWhat := none)
      (damageNoteOpt : Option TriggerDamageNote := none)
      (countersOpt : Option CounterSelector := none)
      (tokenKindOpt : Option TokenKind := none)
      (subtypeOpt : Option String := none)
      (tokenNoteOpt : Option TriggerTokenNote := none)
      (tappedOrAttach : Bool := false)
      (whoPlayerOpt : Option PlayerSelector := none)
      (whoObjOpt : Option ObjectSelector := none)
      (amountOpt : Option NumberSelector := none)
      (toughnessOpt : Option NumberSelector := none)
  /-- Scry, surveil, mill, draw, or gain/lose life (CR 118.2 / CR 118.3a / CR 121 / CR 701.13 / CR 701.18 / CR 701.25).
  Scry, as `amount` says. `.fixed` is that many cards.
  Scry 2 is `.scry (.fixed 2)`. Any other count scries that many cards.
  Scry 0 looks at nothing and does not trigger “whenever you scry.” A
  selector that is not a count scries nothing.
  Mill cards (CR 701.13), as `amount` and `who` say. `millNote` says what a
  later step can read.
  Milling zero cards changes nothing. A library that runs out logs that
  it is empty and mills nothing further.
  The controller mills `n` with `.mill (.fixed n)`.
  The announced player mills `n` with `.mill (.fixed n) (.target .player)`.
  An illegal target mills nothing.
  The player who lost life mills that many with
  `.mill .thatManyLost .thatPlayer`.
  The count is the trigger's last-known power. That player's seat is the
  trigger's last-known toughness. A missing count or seat mills nothing.
  The controller mills `n` and remembers those cards with
  `.mill (.fixed n) (note := .milledCards)`.
  Each opponent mills `n`, and a later step sees whether any card was
  milled, with `.mill (.fixed n) .eachOpponent (note := .opponentsMilled)`.
  Any other count is milled by the players the selector names, and the
  note records what it says. A missing count or player mills nothing.
  `who` draws cards or gains/loses life (CR 118.2 / CR 118.3a / CR 121), as `amount` says.
  `.fixed` is that many cards.
  The controller is `.you`.
  The controller draws `n` is `.draw (.fixed n)`.
  A card for each Human tapped by an earlier step is `.draw .forEachTappedHuman`.
  A card for each graveyard with seven or more cards is `.draw .perFatGraveyard`.
  Cards equal to the hand an earlier step discarded are `.draw .discardedHand`.
  X cards, where X is the mana spent to cast the triggering spell, are
  `.draw .equalToManaSpent`. Spending none skips later steps.
  The targeted opponent may have you draw a card is
  `.draw (.fixed 1) .opponentHasYou`.
  Optional as `.may (.draw (.fixed 1) .opponentHasYou) (.sequence [])`. Declining that
  offer mills and that player loses life; it does not skip.
  The enchanted creature's controller draws a card is
  `.draw (.fixed 1) (.controller .enchanted)`. Nothing enchanted draws nothing.
  Cards until the controller has ten in hand are
  `.draw (.upToHandSize 10)`. A hand that already has ten draws nothing.
  One card for each permanent of `ty` the controller controls is
  `.draw (.perControlled ty)`.
  You gain life (CR 118.2), as `amount` says.
  You gain `n` life is `.gainLife (.fixed n)`.
  Life equal to the targeted card's power is `.gainLife .equalToTargetPower`.
  Inside `sequence`, that power is read when the sequence starts, before an
  earlier step moves the card.
  1 life for each permanent destroyed by an earlier step is
  `.gainLife .forEachDestroyedThisWay`.
  1 life for each other creature you control is `.gainLife .perOtherCreature`.
  Life equal to the Equipment attached to the source is
  `.gainLife .attachedEquipment`. A source that has left uses its last-known
  power. Zero gains nothing.
  Any other count gains that much life. A count that cannot be read
  gains nothing. -/
  | playerResource (isManaOrCast : Bool := false)
      (isDrawOrLife : Bool := false) (isLife : Bool := false) (lose : Bool := false)
      (surveil : Option TriggerSurveilNote := none)
      (millNoteOpt : Option TriggerMillNote := none)
      (whatCostOpt : Option CostSelector := none) (noteOpt : Option ManaSpendNote := none)
      (originOpt : Option TriggerCastFrom := none) (maxMvOpt : Option TriggerCastMv := none)
      (costOpt : Option TriggerCastCost := none) (castNoteOpt : Option TriggerCastNote := none)
      (types : Array ManaType := #[])
      (whoOpt : Option PlayerSelector := none) (amountOpt : Option NumberSelector := none)
  /-- Tap or untap permanents, discard cards, return cards to a hand, or put a card onto a library (CR 400.7 / CR 401 / CR 701.8 / CR 701.21).
  Discard cards, as `what` says.
  One card from the controller is `.discard` (`.cards`).
  Inside `.may _ _ .ifYouDo`, one card is optional: declining skips the follow-up.
  Each opponent discards one is `.discard (.cards 1 .eachOpponent)`.
  The announced opponent discards `n` is `.discard (.cards n (.target .opponent))`.
  The controller's hand, noting how many cards were discarded, is
  `.discard .hand`.
  Optional as `.may (.discard .hand) (.sequence [])`. Declining leaves the note
  empty so the following draw and damage steps do nothing.
  `n` cards when mana was spent to cast the triggering spell is
  `.«if» .manaSpent (.discard (.cards n))`. Spending none discards nothing.
  The announced opponent reveals their hand and discards a nonland you
  choose with `.discard .chosenNonland`.
  `.cards n` for any other player discards that many cards. A selector that
  does not name cards discards nothing.
  Tap or untap permanents, as `what` and `tapped` say.
  Any number of untapped Humans you control is `.tap .humans`.
  Choosing none taps nothing. Optional as `.may (.tap .humans) (.sequence [])`.
  The creature the source enchants is `.tap .enchanted`.
  Nothing enchanted taps nothing. A missing source taps nothing.
  The announced permanent, if it is still on the battlefield, is
  `.tap (.target .ifPresent)`. A missing target taps nothing.
  The announced permanent, while it is still a legal target, is
  `.tap .target`. An illegal target is reported.
  Wrapping one in `may` is that tap.
  The creature this Aura enchants, while the Aura remains, is
  `.tap .enchantedWhileSource`.
  Any other permanent the selector names is tapped or untapped. A card or a hand
  is not.
  Pay a cost or add mana (CR 106 / CR 118).
  Pay `what`. Inside `.may _ _ .ifYouDo`, declining skips the follow-up.
  `{n}` is `.pay (.mana #[.generic n])`. `{1}{G}{U}` is
  `.pay (.mana #[.generic 1, .colored .green, .colored .blue])`.
  Sacrificing another creature is `.pay (.sacrifice (.fixed 1) .another)`.
  Its power is noted.
  Sacrificing another creature or artifact is
  `.pay (.sacrifice (.fixed 1) .anotherCreatureOrArtifact)`.
  Sacrificing an artifact is `.pay (.sacrifice (.fixed 1) .artifact)`.
  Discarding a card is `.pay (.discard (.fixed 1) .card)`.
  Discarding a nonland card is `.pay (.discard (.fixed 1) .nonland)`.
  Sacrificing an artifact, or discarding a card, is
  `.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card])`.
  Sacrificing an artifact, or discarding a nonland card, is
  `.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .nonland])`.
  Add mana, as `amount` says. `types` is the printed mana, and `note`
  describes any color choice or spending restriction.
  Adding those types once is `.addMana types`.
  Adding them `n` times is `.addMana types (.fixed n)`.
  Zero times adds nothing.
  {G} for each charge counter on the source is
  `.addMana #[.colored .green] .perChargeCounter`.
  A source that has left uses its last-known charge counters.
  Any other count adds the printed types that many times. Zero adds
  nothing. A count that cannot be read adds nothing.
  Put counters, create tokens, or amass (CR 111.10 / CR 122 / CR 701.34 / CR 701.47).
  Each creature you control is `.putCounters (.ofKind .plusOnePlusOne) .youControl`.
  Each permanent of a subtype is
  `.putCounters (.ofKind .plusOnePlusOne) (.youControl (.subtype s))`.
  One counter, or two with the city's blessing, is
  `.putCounters (.ofKind .plusOnePlusOne) (.youControl .citysBlessing)`.
  Each other creature you control is
  `.putCounters (.ofKind .plusOnePlusOne) .eachOther`.
  +1/+1 counters equal to the last-known mana value, on the target, is
  `.putCounters .plusOneLastKnownMv .permanent`.
  A loyalty counter on the source is `.putCounters (.ofKind .loyalty) .source`.
  The source's last-known counters on the target are
  `.putCounters .sourceCounters .permanent`.
  A charge counter on the source is `.putCounters (.ofKind .charge) .source`.
  A quest counter on the source is `.putCounters (.ofKind .quest) .source`.
  Hone counters for each creature the opponent controls are
  `.putCounters .honePerOpponent .source`.
  A plan counter on the source is `.putCounters (.ofKind .plan) .source`.
  Later steps do not run if the source has left.
  A +1/+1 counter you put on the target is
  `.putCounters (.ofKind .plusOnePlusOne) (.permanent true)`.
  The noted number of +1/+1 counters on the created token is
  `.putCounters .plusOneNoted .createdToken`.
  An invasion counter on the source is `.putCounters (.ofKind .invasion) .source`.
  A trample counter on the target is `.putCounters (.ofKind .trample) .permanent`.
  An influence counter on the source, when the opponent is still legal, is
  `.putCounters (.ofKind .influence) .source`. An illegal target skips later steps.
  A loyalty counter on the target is `.putCounters (.ofKind .loyalty) .permanent`.
  +1/+1 counters equal to the sacrificed creature's power are
  `.putCounters .plusOneSacrificedPower .source`.
  `n` +1/+1 counters on the announced permanent are
  `.putCounters (.ofKind .plusOnePlusOne n) .permanent`.
  An indestructible counter on the announced permanent is
  `.putCounters (.ofKind .indestructible) .permanent`.
  A double strike counter is `.putCounters (.ofKind .doubleStrike) .permanent`.
  A burden counter is `.putCounters (.ofKind .burden) .permanent`.
  A stun counter is `.putCounters (.ofKind .stun) .permanent`.
  The keyword counters the announced creature has that the source does not are
  `.putCounters .missingKeywordsFromTarget .source`. An illegal target or a
  missing source puts nothing.
  One +1/+1 counter on each announced creature you control, up to the life
  gained (the trigger's last-known power), is
  `.putCounters (.ofKind .plusOnePlusOne) .eachUpToLastKnown`.
  None, or zero life, puts counters on nothing. An illegal permanent is
  reported and skipped. Extra announced permanents are ignored.
  Any other permanent the selector names gets `n` counters of that kind.
  A card or a hand receives none.
  Put later ability `thenDo` on the stack (“When you do”), or arm it
  for a later event (`howOpt = none`), or look at cards from the top of a library (`howOpt = some how`), as `how` and `whoOpt` say, then resolve `thenDo` for the cards that were found.
  Another nonattacking creature gains indestructible is
  `.queueReflexive (.grant (.keywords Keyword.indestructible) .target)`.
  Trick Arrows, paying up to three times, is
  `.queueReflexive (.chooseModes TriggerResolution.trickArrowModes .alreadyChosen)`.
  An indestructible counter is
  `.queueReflexive (.putCounters (.ofKind .indestructible) .permanent)`.
  Controlling an opponent during their next turn is
  `.queueReflexive (.gainControl .duringNextTurn)`.
  An opponent exiling the top five, and casting up to two, is
  `.queueReflexive (.exile (.opponentTop 5) (.mayCastUpTo 2))`.
  A graveyard creature returning tapped and attacking is
  `.queueReflexive (.put .creatureCard .tapped (.entering [.attacking, .counter .finality]))`.
  Destroying an opposing nonland is `.queueReflexive (.destroy .target)`.
  A creature with haste that can't be blocked except by haste is
  `.queueReflexive (.cant (.beBlockedExceptByHaste .target))`.
  Up to two instants or sorceries from the graveyard are
  `.queueReflexive (.returnToHand (.graveyardInstants 2))`.
  A +1/+1 counter on target creature is
  `.queueReflexive (.putCounters (.ofKind .plusOnePlusOne) .permanent)`.
  Damage to any target is `.queueReflexive (.dealDamage (.fixed n) .target)`.
  Damage equal to the source's +1/+1 counters is
  `.queueReflexive (.dealDamage .plusOneCounters .target)`.
  A source that has left queues nothing.
  Exile and copy a milled spell is
  `.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying)`.
  After opponents mill, that is
  `.«if» .opponentsMilled (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying))`.
  Divided damage is
  `.queueReflexive (.dealDamage (.fixed amount) .target .divided)`.
  After the Plan is sacrificed, that is
  `.«if» .planWasSacrificed (.queueReflexive (.dealDamage (.fixed amount) .target .divided))`.
  A Plan that was not sacrificed queues nothing.
  Whenever you attack this turn, +1/+1 for each Plains, is
  `.queueReflexive (.pump .perPlains .perPlains .target)`.
  That arms the attack trigger. It does not put an ability on the stack
  now. Any other follow-up is put on the stack and resolves as that
  follow-up. It keeps the targets this ability already has.
  The top `n` cards of your library, a random creature from among them
  onto the battlefield, and the rest on the bottom in a random order, is
  `.revealLibrary (.top n) (.put .randomCreature)`. Looking at zero cards,
  or no creature among them, logs that no creature was revealed. With
  `norandom` and more than one creature, that choice waits.
  Cards from the top of your library until a creature, onto the battlefield
  when its mana value is at most the lands you control and into your hand
  otherwise, is
  `.revealLibrary .untilCreature (.ifElse .revealedManaValueAtMostLands (.put .revealed) (.returnToHand .revealed))`.
  Cards from the top of your library until a Saga, onto the battlefield, is
  `.revealLibrary .untilSaga (.put .revealed)`.
  An empty library for those two cases changes nothing.
  Cards from the top of the damaged player's library until an instant or
  sorcery, exiled face up for `.mayCast .impulse`, is
  `.revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer`.
  A missing damaged player is the controller's opponent. An empty library
  still remembers the impulse, with nothing exiled.
  Cards from the announced player's library until a nonland. You may put
  a +1/+1 counter on the source. If you don't, you may cast that nonland
  until end of turn and spend mana of any type. That is
  `.revealLibrary .untilNonland (.may (.putCounters (.ofKind .plusOnePlusOne) .source) (.exile .top .forLater .anyManaThisTurn) .ifYouDont) .announced`.
  A missing player is reported. An empty library exiles nothing. A source
  that has left grants the cast without asking for the counter.
  The top `n` cards. You may cast a spell from among them with mana value at
  most the greatest power among attacking creatures you control, without
  paying its mana cost. The rest go on the bottom in a random order. That is
  `.revealLibrary (.top n) (.mayCast .looked .greatestAttackingPower .withoutPaying)`.
  An empty library is reported. No attacker limits the mana value to zero.
  Whose library is a `PlayerSelector`.
  Any other combination reveals the cards `how` and `who` name, then
  resolves `thenDo`. A player the selector does not name reveals nothing.
  Sacrifice or destroy permanents (CR 701.7 / CR 701.17).
  Sacrifice a permanent. `what` says who sacrifices and which permanent.
  `sacNote` says what a later step can read.
  The announced opponent sacrifices a creature of their choice with
  `.sacrifice .opponentChosenCreature`.
  Each player sacrifices a creature of their choice with
  `.sacrifice .eachPlayersCreature`.
  The defending player sacrifices a least-power creature with
  `.sacrifice .leastPower`.
  Each opponent sacrifices a creature that dealt combat damage to you with
  `.sacrifice .combatDamager`.
  The source is sacrificed with `.sacrifice .source`.
  The controller sacrifices the source with
  `.sacrifice (.sacrificedSource .controllerSacrifices)`.
  The source moves as sacrificed, without a token-sacrifice trigger, with
  `.sacrifice (.sacrificedSource .movedAsSacrificed)`.
  `.sacrifice (.sacrificedSource .isSacrificed)` is the same as
  `.sacrifice .source`.
  The Plan, if it is still on the battlefield, is `.sacrifice .plan`.
  The Plan, noting whether the sacrifice happened, is
  `.sacrifice .plan .forReflexive`.
  You may sacrifice another creature with `.may (.sacrifice .another) (.sequence [])`.
  Each opponent sacrifices a nontoken creature of their choice with
  `.sacrifice .chosenNontokenCreature`.
  Any other permanent the selector names is sacrificed. `.noted` records
  that a sacrifice happened. `.forReflexive` records it for the next
  reflexive step. A card or a hand is not sacrificed.
  Destroy permanents. `what` says which, and `destroyNote` says what a later
  step can read.
  Opponents' artifacts and enchantments, counted for the next step, are
  `.destroy .oppArtifactsEnchantments (note := .countDestroyed)`.
  Only permanents that actually leave are counted.
  The permanent an earlier step dealt damage to is
  `.destroy .permanentDealtDamage`.
  The announced creature, noting its controller and power, is
  `.destroy .target (note := .forAmass)`. No target means no player amasses.
  The announced permanent is `.destroy .target`.
  The announced token, when this ability's target is a player, is
  `.destroy .target (note := .chosenToken)`.
  The source is `.destroy .source`.
  The enchanted creature is `.destroy .enchanted`.
  The target, while the source remains, is `.destroy (.target .whileSource)`.
  Any other permanent the selector names is destroyed. A card or a hand
  is not.
  Apply each resolution in order (`howOpt = none`, CR 608.2b), or resolve these modes as `how` says (`howOpt = some how`, CR 700.2).
  Return a graveyard card, then gain life equal to its power, is `.sequence [.returnToHand .graveyardCard, .gainLife .equalToTargetPower]`.
  Draw, then bottom a card if you control no legendary, is
  `.sequence [.draw (.fixed 1), .«if» (.not (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1))) (.putOnLibrary .bottom .cardFromHand)]`.
  Remove a hope counter, draw if one was removed, then sacrifice and gain
  life if none remain, is
  `.sequence [.removeCounters .hope .source, .«if» .removedHope (.draw (.fixed 1)), .«if» (.not .hopeOnSource) (.sequence [.sacrifice .source, .gainLife (.fixed 4)])]`.
  A step that asks a player to choose pauses the later steps until that
  choice finishes; they are still part of this resolution. Tap any number
  of Humans, then draw that many, is
  `.sequence [.may (.tap .humans) (.sequence []), .draw .forEachTappedHuman]`.
  Create one token, then attach the source to it, is
  `.sequence [.createTokens kind (.fixed 1) false, .attach .source .createdToken]`.
  Gain life, then you may search a basic land onto the top, is
  `.sequence [.gainLife (.fixed n), .searchLibrary (.put .basicLandOnTop)]`.
  Destroy opponents' artifacts and enchantments, then gain 1 life for each
  one actually destroyed, is
  `.sequence [.destroy .oppArtifactsEnchantments (note := .countDestroyed), .gainLife .forEachDestroyedThisWay]`.
  Put a +1/+1 counter on each other creature you control, then gain 1 life
  for each other creature you control, is
  `.sequence [.putCounters (.ofKind .plusOnePlusOne) .eachOther, .gainLife .perOtherCreature]`.
  Deal `n` damage to the target, then destroy it if that damage marked a
  permanent of this subtype, is
  `.sequence [.dealDamage (.fixed n) .target .markedPermanent, .«if» (.dealtDamageToSubtype subtype) (.destroy .permanentDealtDamage)]`.
  Destroy the announced creature, then its controller amasses that power, is
  `.sequence [.destroy .target (note := .forAmass), .amass .notedPower (who := .controller .target), .«if» .youControlledDestroyed (.draw (.fixed 1))]`.
  Return another permanent to its owner's hand, then put a +1/+1 counter on
  the source if one was actually returned, is
  `.sequence [.returnToHand .permanent .returnedPermanent, .«if» .returnedPermanent (.putCounters (.ofKind .plusOnePlusOne) .source)]`.
  Other creatures you control of these subtypes get +P/+T, and creatures
  your opponents control get +oppP/+oppT, is
  `.sequence [.pump (.fixed p) (.fixed t) (.intersection [.creaturesYouControl, .union (subtypes.toList.map .othersOfSubtype)]), .pump (.fixed oppP) (.fixed oppT) .opponentsCreatures]`.
  Gain 1 life, draw, or put a +1/+1 counter on each creature you control
  when this is the first, second, or third resolve this turn (Belladonna
  Took), is
  `.sequence [.noteResolveThisTurn 3, .«if» (.nthResolve 1) (.gainLife (.fixed 1)), .«if» (.nthResolve 2) (.draw (.fixed 1)), .«if» (.nthResolve 3) (.putCounters (.ofKind .plusOnePlusOne) .youControl)]`.
  Deal the sacrificed creature's power, then amass Goblins for the excess
  (Bolg), is
  `.sequence [.dealDamage .lastKnownPower .permanent .excess, .amass .notedExcess]`.
  Put a plan counter, then scry, is
  `.sequence [.putCounters (.ofKind .plan) .source, .scry (.fixed n)]`.
  Put a trample counter on the target, then make it a Bear, is
  `.sequence [.putCounters (.ofKind .trample) .permanent, .grant .bearType .target]`.
  Draw, discard, and a land discarded this way enters tapped, is
  `.sequence [.draw (.fixed 1), .discard (.cards 1), .put .discardedLand (how := .tapped)]`.
  Put an influence counter, scry 2, then offer the opponent's choice
  (Palantír of Orthanc), is
  `.sequence [.putCounters (.ofKind .influence) .source, .scry (.fixed 2), .may (.draw (.fixed 1) (who := .opponentHasYou)) (.sequence [])]`.
  Grant keywords, then a +1/+1 counter if the target is a creature and a
  loyalty counter if it is a planeswalker, is
  `.sequence [.grant (.keywords k) .target, .«if» (.atLeast (.count (.target .creature)) (.fixed 1)) (.putCounters (.ofKind .plusOnePlusOne) .permanent), .«if» (.atLeast (.count (.target .planeswalker)) (.fixed 1)) (.putCounters (.ofKind .loyalty) .permanent)]`.
  The target gets +3/+0 and gains first strike until end of turn, is
  `.sequence [.pump (.fixed 3) (.fixed 0) .target, .grant (.keywords Keyword.firstStrike) .target]`.
  +P/+T and trample is
  `.sequence [.pump (.fixed p) (.fixed t) .target, .grant (.keywords Keyword.trample) .target]`.
  Becoming an artifact and gaining indestructible is
  `.sequence [.becomeArtifact, .grant (.keywords Keyword.indestructible) .target]`.
  Tap and a stun counter is
  `.sequence [.tap .target, .putCounters (.ofKind .stun) .permanent]`.
  Destroy the target, then its controller creates a Treasure, is
  `.sequence [.destroy .target, .createTokens .treasure (.fixed 1) false (who := .controller .target)]`.
  You may put an artifact from your hand onto the battlefield, then attach
  it to the source if it is Equipment, is
  `.sequence [.may (.put .artifactFromHand (note := .forAttach)) (.sequence []), .«if» (.atLeast (.count .putEquipment) (.fixed 1)) (.attach .putArtifact .notedHost)]`.
  Alliance is `.chooseModes TriggerResolution.allianceModes .oneUnusedThisTurn`.
  Gollum is `.chooseModes TriggerResolution.gollumModes .oneUnused`.
  Chosen up to X, in printed order, is
  `.chooseModes TriggerResolution.upToXModes .alreadyChosen`.
  A +1/+1 counter on the source, or removing a counter to draw, is
  `.chooseModes TriggerResolution.hydeModes .plusOneOrRemoveCounter`.
  One unused Vision mode this turn is
  `.chooseModes TriggerResolution.visionModes .vision`.
  The controller may resolve `action`. `when` says which outcome resolves
  `follow`. `.ifYouDont` is the default: declining resolves `follow`, and
  performing `action` skips it. `.ifYouDo` resolves `follow` only when
  `action` is performed. Declining, or being unable to perform `action`,
  skips that follow-up.
  A choice that already includes decline is that choice, so the player
  is not asked twice. You may draw X cards, where X is the mana spent to
  cast the triggering spell, then discard two, is
  `.may (.sequence [.draw .equalToManaSpent, .«if» .manaSpent (.discard (.cards 2))]) (.sequence [])`.
  You may tap any number of untapped Humans is `.may (.tap .humans) (.sequence [])`.
  You may sacrifice another creature is `.may (.sacrifice .another) (.sequence [])`.
  You may put an artifact from your hand onto the battlefield is
  `.may (.put .artifactFromHand (note := .forAttach)) (.sequence [])`.
  You may discard your hand is `.may (.discard .hand) (.sequence [])`.
  The targeted opponent may have you draw a card is
  `.may (.draw (.fixed 1) (who := .opponentHasYou)) (.sequence [])`. Declining that offer mills and
  that player loses life; it does not skip.
  You may put a land card from your hand onto the battlefield tapped is
  `.may (.put .landFromHand (how := .tapped)) (.sequence [])`.
  `SharedTrigger.may a` resolves as `.may` of `a`'s resolution and an empty sequence.
  Declining, or being unable to put a creature of `subtype` with mana value
  at most `maxMv` from your hand, draws a card with
  `.may (.put (.creatureFromHand subtype maxMv)) (.draw (.fixed 1))`.
  Declining with no other effect is `.may action (.sequence [])`.
  You may discard a card to draw `n` is `.may (.discard (.cards 1)) (.draw (.fixed n)) .ifYouDo`.
  `SharedTrigger.mayTo a b` resolves as `.may` of each step's resolution, `.ifYouDo`.
  You may pay `{n}` to draw is `.may (.pay (.mana #[.generic n])) (.draw (.fixed 1)) .ifYouDo`.
  Paying `{n}` to put a +1/+1 counter on the source and draw is
  `.may (.pay (.mana #[.generic n])) (.sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .draw (.fixed 1)]) .ifYouDo`.
  You may sacrifice another creature for +1/+1 counters equal to its power is
  `.may (.pay (.sacrifice (.fixed 1) .another)) (.putCounters .plusOneSacrificedPower .source) .ifYouDo`.
  You may pay `{1}{G}{U}` to return this from the graveyard is
  `.may (.pay (.mana #[.generic 1, .colored .green, .colored .blue])) (.returnToHand .source) .ifYouDo`.
  You may sacrifice another creature or artifact to draw and create a Treasure is
  `.may (.pay (.sacrifice (.fixed 1) .anotherCreatureOrArtifact)) (.sequence [.draw (.fixed 1), .createTokens .treasure (.fixed 1) false]) .ifYouDo`.
  You may discard your hand to draw `n` is `.may (.discard .hand) (.draw (.fixed n)) .ifYouDo`.
  You may draw for each permanent of a type, and each opponent draws if you do, is
  `.may (.draw (.perControlled ty)) (.draw (.fixed 1) (who := .eachOpponent)) .ifYouDo`.
  You may sacrifice an artifact or discard a card to draw is
  `.may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card])) (.draw (.fixed 1)) .ifYouDo`.
  You may sacrifice another creature to destroy an opposing nonland is
  `.may (.pay (.sacrifice (.fixed 1) .another)) (.queueReflexive (.destroy .target)) .ifYouDo`.
  You may sacrifice an artifact or discard a nonland to deal 2 damage is
  `.may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .nonland])) (.queueReflexive (.dealDamage (.fixed 2) .target)) .ifYouDo`.
  You may tap this to grant indestructible is
  `.may (.tap .source) (.queueReflexive (.grant (.keywords Keyword.indestructible) .target)) .ifYouDo`.
  You may pay {1} to put a +1/+1 counter on target creature is
  `.may (.pay (.mana #[.generic 1])) (.queueReflexive (.putCounters (.ofKind .plusOnePlusOne) .permanent)) .ifYouDo`.
  You may pay {1} so a target creature with haste can't be blocked this turn
  except by creatures with haste is
  `.may (.pay (.mana #[.generic 1])) (.queueReflexive (.cant (.beBlockedExceptByHaste .target))) .ifYouDo`.
  You may pay {3}{B} to return a graveyard creature tapped and attacking is
  `.may (.pay (.mana #[.generic 3, .colored .black])) (.queueReflexive (.put .creatureCard .tapped (.entering [.attacking, .counter .finality]))) .ifYouDo`.
  You may have the source deal the damage that caused this to the announced
  target is `.may (.dealDamage .lastKnownPower .target) (.sequence []) .ifYouDo`.
  The amount is the trigger's last-known power. Already used this turn does
  nothing. An illegal target is reported. The source need not still be on
  the battlefield.
  You may choose new targets for the spell that caused this is
  `.may .retargetCause (.sequence []) .ifYouDo`.
  You may pay {1} up to three times, then choose that many modes, is
  `.may (.pay (.mana #[.generic 1])) (.queueReflexive (.chooseModes TriggerResolution.trickArrowModes .alreadyChosen)) .ifYouDo`.
  You may pay {2} to copy the nontoken artifact that caused this is
  `.may (.pay (.mana #[.generic 2])) (.becomeCopy .cause) .ifYouDo`.
  You may exile the discarded card and play it until the end of your next
  turn with
  `.may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo`.
  You may create a 0/4 Wall creature token with defender with
  `.may (.createTokens .wall04defender (.fixed 1) false) (.sequence []) .ifYouDo`.
  Declining creates nothing. -/
  | flowOrReveal (isReflexive : Bool := false)
      (mayWhenOpt : Option TriggerMayWhen := none)
      (revealHowOpt : Option TriggerLibraryHow := none)
      (revealWhoOpt : Option PlayerSelector := none)
      (modeHowOpt : Option TriggerModeHow := none)
      (rs : List Resolution)
  /-- Exile cards. `what` says which cards, `how` says for how long, and
  `note` says what a later step can read.
  Which cards is an `ObjectSelector`.
  The targeted permanent, linked for a leave trigger, is
  `.exile .target .leaveTrigger`.
  The targeted permanent until the source leaves is
  `.exile .target .untilSourceLeaves`.
  The top card, playable until the end of your next turn, is
  `.exile .top .playUntilNextTurn`.
  The top card, playable this turn, and +2/+1 on the source when it is a
  Hero, is `.exile .top .playThisTurn .ifHero`. You may do so with
  `.may (.exile .top .playThisTurn .ifHero) (.sequence [])`.
  A missing source still exiles the card. An empty library exiles nothing.
  Each announced permanent until the source leaves is
  `.exile (.target .eachPermanent) .untilSourceLeaves`.
  The targeted permanent until the next end step is
  `.exile .target .nextEndStep`.
  Targeted lands, remembered so they return tapped, are
  `.exile .landsYouControl .forLater .lands`.
  Another creature until the source leaves, remembered for a copy, is
  `.exile .target .untilSourceLeaves .copyAndHost`.
  A graveyard card, remembered so it can be played, is
  `.exile .graveyardCard .forLater .playCard`.
  Cards from the damaged player's library until an instant or sorcery,
  remembered for `.mayCast .impulse`, are
  `.exile .top .forLater .impulse` inside `revealLibrary`. Outside that
  resolution, the exile does nothing.
  The nonland from `revealLibrary .untilNonland`, cast with mana of any
  type until end of turn when the counter is declined, is
  `.exile .top .forLater .anyManaThisTurn` inside that resolution.
  Outside it, the exile does nothing.
  The announced permanent, with no return, is `.exile .target .forLater`.
  The source is `.exile .source .forLater`.
  The enchanted creature is `.exile .enchanted .forLater`.
  The target, while the source remains, is
  `.exile (.target .whileSource) .forLater`.
  The announced nonland the controller still controls, other than the
  source, exiled and returned immediately, is
  `.exile .target .returnImmediately`. Choosing none does nothing.
  While the source is harnessed is
  `.«if» (.atLeast (.count .harnessedSource) (.fixed 1)) (.exile .target .returnImmediately)`.
  An unharnessed source is reported and exiles nothing.
  The announced nontoken artifact or creature, returned tapped, is
  `.exile .target .returnTapped`. Choosing none does nothing.
  You may exile the card recorded as this trigger's last-known power and
  play it until the end of your next turn with
  `.may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo`.
  A card that has left your graveyard is reported. No recorded card is
  reported. Declining exiles nothing.
  Any other permanent the selector names is exiled as `how` and `note` say.
  A graveyard card, the top of a library, a linked exile, a milled card, a
  discarded card, or a card an earlier reveal found is exiled the same way.
  `.top` with `.impulse` or `.anyManaThisTurn` exiles nothing unless an
  earlier reveal found a card. A hand or an unmade choice exiles nothing.
  Any other graveyard card the selector names, the top card of your library,
  or the source in its owner's graveyard is put onto the battlefield as
  `how` and `note` say. `.revealed` and `.randomCreature` use the cards an
  earlier reveal found. Outside that reveal, both do nothing. A permanent
  already on the battlefield is not put again. -/
  | zoneOrTap (isTapDiscardOrReturn : Bool := false)
      (returnNoteOpt : Option TriggerReturnNote := none)
      (placeOpt : Option TriggerLibraryPlace := none)
      (putHowOpt : Option TriggerPutHow := none)
      (putNoteOpt : Option TriggerPutNote := none)
      (exileHowOpt : Option TriggerExileHow := none)
      (exileNoteOpt : Option TriggerExileNote := none)
      (sacNoteOpt : Option TriggerSacrificeNote := none)
      (destroyNoteOpt : Option TriggerDestroyNote := none)
      (isDiscard : Bool := false) (tapped : Bool := true)
      (what : ObjectSelector := .cards)
deriving Repr, BEq

instance : Inhabited Resolution where
  default := .combatCountersOrTokens none none none none none none false none (some .source) (some .greatestPower) (some .greatestPower)

namespace Resolution

  @[match_pattern] abbrev pump (power toughness : NumberSelector)
      (who : ObjectSelector := .target) : Resolution :=
    .combatCountersOrTokens none none none none none none false none (some who) (some power) (some toughness)
  @[match_pattern] abbrev dealDamage (amount : NumberSelector) (who : ObjectSelector)
      (note : TriggerDamageNote := .none) : Resolution :=
    .combatCountersOrTokens none (some note) none none none none false none (some who) (some amount) none
  @[match_pattern] abbrev grant (what : TriggerGrantWhat) (who : ObjectSelector := .target) : Resolution :=
    .combatCountersOrTokens (some what) none none none none none false none (some who) none none
  @[match_pattern] abbrev putCounters (what : CounterSelector) (who : ObjectSelector) : Resolution :=
    .combatCountersOrTokens none none (some what) none none none false none (some who) none none
  @[match_pattern] abbrev exile (what : ObjectSelector) (how : TriggerExileHow)
      (note : TriggerExileNote := .none) : Resolution :=
    .zoneOrTap false none none none none (some how) (some note) none none false false what
  @[match_pattern] abbrev put (what : ObjectSelector) (how : TriggerPutHow := .asPrinted)
      (note : TriggerPutNote := .none) : Resolution :=
    .zoneOrTap false none none (some how) (some note) none none none none false false what
  @[match_pattern] abbrev queueReflexive (followup : Resolution) : Resolution :=
    .flowOrReveal true none none none none [followup]
  @[match_pattern] abbrev revealLibrary (how : TriggerLibraryHow) (thenDo : Resolution)
      (who : PlayerSelector := .you) : Resolution :=
    .flowOrReveal false none (some how) (some who) none [thenDo]
  @[match_pattern] abbrev sequence (rs : List Resolution) : Resolution :=
    .flowOrReveal false none none none none rs
  @[match_pattern] abbrev chooseModes (modes : List Resolution) (how : TriggerModeHow := .one) : Resolution :=
    .flowOrReveal false none none none (some how) modes
  @[match_pattern] abbrev may (action follow : Resolution)
      (when : TriggerMayWhen := .ifYouDont) : Resolution :=
    .flowOrReveal false (some when) none none none [action, follow]

/-- Scry, as `n` says (CR 701.18). -/
@[match_pattern] abbrev scry (n : NumberSelector)
    (surveil : Option TriggerSurveilNote := none) : Resolution :=
  .playerResource false false false false surveil none none none none none none none #[] none (some n)

/-- Mill cards (CR 701.13), as `amount` and `who` say. -/
@[match_pattern] abbrev mill (amount : NumberSelector) (who : PlayerSelector := .you)
    (note : TriggerMillNote := .none) : Resolution :=
  .playerResource false false false false none (some note) none none none none none none #[] (some who) (some amount)

/-- `who` draws cards (CR 121), as `amount` says. -/
@[match_pattern] abbrev draw (amount : NumberSelector)
    (who : PlayerSelector := .you) : Resolution :=
  .playerResource false true false false none none none none none none none none #[] (some who) (some amount)

/-- `who` gains or loses life (CR 118.2 / CR 118.3a), as `amount` says. -/
@[match_pattern] abbrev gainLife (amount : NumberSelector)
    (who : PlayerSelector := .you) (lose : Bool := false) : Resolution :=
  .playerResource false true true lose none none none none none none none none #[] (some who) (some amount)

/-- Tap or untap permanents (CR 701.21), as `who` and `tapped` say. -/
@[match_pattern] abbrev tap (who : ObjectSelector)
    (tapped : Bool := true) : Resolution :=
  .zoneOrTap true none none none none none none none none false tapped who

/-- Discard cards (CR 701.8), as `what` says. -/
@[match_pattern] abbrev discard (what : ObjectSelector := .cards) : Resolution :=
  .zoneOrTap true none none none none none none none none true true what

/-- Pay `what` (CR 118). -/
@[match_pattern] abbrev pay (what : CostSelector) : Resolution :=
  .playerResource true false false false none none (some what) none none none none none #[] none none

/-- Add mana (CR 106), as `amount` says. -/
@[match_pattern] abbrev addMana (types : Array ManaType)
    (amount : NumberSelector := .fixed 1)
    (note : ManaSpendNote := .none) : Resolution :=
  .playerResource true false false false none none none (some note) none none none none types none (some amount)

/-- Return cards to a hand (CR 400.7). -/
@[match_pattern] abbrev returnToHand (what : ObjectSelector := .graveyardCard)
    (note : TriggerReturnNote := .none) : Resolution :=
  .zoneOrTap true (some note) none none none none none none none false false what

/-- Put a card onto a library (CR 401). -/
@[match_pattern] abbrev putOnLibrary (place : TriggerLibraryPlace := .top)
    (what : ObjectSelector := .target) : Resolution :=
  .zoneOrTap true none (some place) none none none none none none false false what

/-- Sacrifice a permanent (CR 701.17). -/
@[match_pattern] abbrev sacrifice (what : ObjectSelector)
    (note : TriggerSacrificeNote := .none) : Resolution :=
  .zoneOrTap false none none none none none none (some note) none false false what

/-- Destroy permanents (CR 701.7). -/
@[match_pattern] abbrev destroy (what : ObjectSelector)
    (note : TriggerDestroyNote := .none) : Resolution :=
  .zoneOrTap false none none none none none none none (some note) false false what

/-- Amass `subtype` for `who` (CR 701.47), as `amount` says. -/
@[match_pattern] abbrev amass (amount : NumberSelector)
    (subtype : String := "Goblin") (attachSource : Bool := false)
    (who : PlayerSelector := .you) : Resolution :=
  .combatCountersOrTokens none none none none (some subtype) none attachSource (some who) none (some amount) none

/-- Create tokens (CR 111.10). -/
@[match_pattern] abbrev createTokens (kind : TokenKind) (amount : NumberSelector)
    (tapped : Bool := false) (who : PlayerSelector := .you)
    (note : TriggerTokenNote := .none) : Resolution :=
  .combatCountersOrTokens none none none (some kind) none (some note) tapped (some who) none (some amount) none

/-- You may cast a spell (CR 601). -/
@[match_pattern] abbrev mayCast (origin : TriggerCastFrom) (maxMv : TriggerCastMv)
    (cost : TriggerCastCost) (note : TriggerCastNote := .none) : Resolution :=
  .playerResource true false false false none none none none (some origin) (some maxMv) (some cost) (some note) #[] none none

/-- A resolution that is not a spell shape. It does not play an extra land. -/
@[match_pattern] abbrev unrecognized : Resolution :=
  .playerResource true false false false none none none none none none none none #[] none none

/-- Search a library (CR 701.23), then resolve `thenDo` for the card that was found. -/
@[match_pattern] abbrev searchLibrary (thenDo : Resolution) : Resolution :=
  .revealLibrary .search thenDo .you

/-- Attach `what` to `host` (CR 701.3). -/
@[match_pattern] abbrev attach (what host : ObjectSelector) : Resolution :=
  .grant (.attachTo host) what

/-- Resolve `thenDo` when `cond` holds (CR 608.2c). -/
@[match_pattern] abbrev «if» (cond : ConditionSelector) (thenDo : Resolution) : Resolution :=
  .chooseModes [thenDo] (.«if» cond)

/-- Connive (CR 701.48). `who` says which creature. -/
@[match_pattern] abbrev connive (who : ObjectSelector := .source) : Resolution :=
  .grant .connive who

/-- A creature fights, or deals damage equal to its power (CR 701.12). `who` says
which creature, and `how` says which. -/
@[match_pattern] abbrev fight (who : ObjectSelector := .source) (how : TriggerFightHow := .mutual) : Resolution :=
  .grant (.fight how) who

/-- Resolve `r` unless its controller pays `{n}` (CR 118.12). -/
@[match_pattern] abbrev unlessPays (r : Resolution) (n : Nat) : Resolution :=
  .chooseModes [r] (.unlessPays n)

/-- Cascade: exile until a cheaper nonland, then you may cast it (CR 702.85). -/
@[match_pattern] abbrev cascade : Resolution :=
  .grant .cascade .source

/-- The Ring tempts you (CR 701.54). -/
@[match_pattern] abbrev ringTempts : Resolution :=
  .grant .ringTempts .youIfCast

/-- There is an additional combat phase after this one (CR 500.8). -/
@[match_pattern] abbrev additionalCombatPhase : Resolution :=
  .grant .additionalCombatPhase .youIfCast

/-- You win the game (CR 104.2a). -/
@[match_pattern] abbrev winTheGame : Resolution :=
  .grant .winTheGame .youIfCast

/-- Counter the targeted spell (CR 701.5). -/
@[match_pattern] abbrev counter : Resolution :=
  .grant .counterSpell .target

/-- Surveil, as `n` and `note` say (CR 701.25). -/
@[match_pattern] abbrev surveil (n : NumberSelector) (note : TriggerSurveilNote := .none) : Resolution :=
  .scry n (some note)

/-- A player loses life (CR 118.3a), as `amount` and `who` say. -/
@[match_pattern] abbrev loseLife (amount : NumberSelector) (who : PlayerSelector := .you) : Resolution :=
  .gainLife amount who true

/-- Untap permanents, as `who` says. -/
@[match_pattern] abbrev untap (who : ObjectSelector := .target) : Resolution :=
  .tap who false

/-- Resolve `whenTrue` when `cond` holds, and `whenFalse` otherwise. -/
@[match_pattern] abbrev ifElse (cond : ConditionSelector) (whenTrue whenFalse : Resolution) : Resolution :=
  .chooseModes [whenTrue, whenFalse] (.ifElse cond)

/-- The controller chooses one of these resolutions. -/
@[match_pattern] abbrev or (rs : List Resolution) : Resolution :=
  .chooseModes rs .one

/-- Proliferate `amount` times (CR 701.34), or give `who` another counter of each kind on it. -/
@[match_pattern] abbrev proliferate (amount : NumberSelector := .fixed 1) (who : ObjectSelector := .youControl) : Resolution :=
  .putCounters (.eachKindOnIt amount) who

/-- Remove counters. `what` says which, and `who` says from whom. -/
@[match_pattern] abbrev removeCounters (what : TriggerRemoveWhat) (who : ObjectSelector) : Resolution :=
  .putCounters (.remove what) who

/-- A player reveals cards from their hand (CR 701.16), as `count` says, then resolves `thenDo`. -/
@[match_pattern] abbrev revealFromHand (count : TriggerRevealCount) (thenDo : Resolution) : Resolution :=
  .revealLibrary (.fromHand count) thenDo .you

/-- A permanent loses `what`, as `who` says (CR 613.1f Layer 6). -/
@[match_pattern] abbrev lose (what : AbilitySelector) (who : ObjectSelector := .target) : Resolution :=
  .grant (.lose what) who

/-- `action` says what can't be done, and who can't do it (CR 613.1f / CR 508 / CR 509). -/
@[match_pattern] abbrev cant (action : ActionSelector) : Resolution :=
  .grant (.cant action) .target

/-- Until end of turn, `who` becomes an artifact in addition to its other types (CR 613.1d Layer 4). -/
@[match_pattern] abbrev becomeArtifact (who : ObjectSelector := .target) : Resolution :=
  .grant .artifact who

/-- `who` becomes prepared (or unprepared when `prepared = false`). -/
@[match_pattern] abbrev becomePrepared (who : ObjectSelector := .target) (prepared : Bool := true) : Resolution :=
  .grant (.prepared prepared) who

/-- Until end of turn, `who`'s base power and toughness become `power` and `toughness` (CR 613.4b Layer 7b). -/
@[match_pattern] abbrev setBasePT (power toughness : NumberSelector) (who : ObjectSelector := .target) : Resolution :=
  .grant (.basePT power toughness) who

/-- Gain control of the announced permanents, as `how` says (CR 613.1b Layer 2). -/
@[match_pattern] abbrev gainControl (how : TriggerControlHow) : Resolution :=
  .grant (.control how) .target

/-- The source becomes a copy of `of` (CR 613.1a Layer 1). -/
@[match_pattern] abbrev becomeCopy (of : ObjectSelector) : Resolution :=
  .grant (.copy of) .source

/-- If the targeted permanent would die this turn, exile it instead (CR 614.1). -/
@[match_pattern] abbrev replace : Resolution :=
  .grant .replace .target

/-- Spells of `which` cost less this turn, as `n` says (CR 601.2f). -/
@[match_pattern] abbrev spellsCostLess (which : SpellCostLess) (n : NumberSelector) : Resolution :=
  .grant (.spellsCostLess which n) .youIfCast

/-- Investigate (create a Clue; CR 701.36). -/
@[match_pattern] abbrev investigate (who : PlayerSelector := .you) : Resolution :=
  .grant .investigate (.player who)

/-- Empower Jace, as `n` says (Reality Fracture). -/
@[match_pattern] abbrev empowerJace (n : NumberSelector) : Resolution :=
  .grant (.empowerJace n) .youIfCast

/-- Recruit. “recruit” is `.recruit`. “you recruit” is `.recruit .you`. -/
@[match_pattern] abbrev recruit (who : PlayerSelector := .recruit) : Resolution :=
  .grant (.recruit who) .youIfCast

/-- Record another resolution of this ability this turn. -/
@[match_pattern] abbrev noteResolveThisTurn (limit : Nat) : Resolution :=
  .grant (.noteResolveThisTurn limit) .source

/-- Resolve the reflexive triggered ability `kind` of an MSH card. -/
@[match_pattern] abbrev mshReflexive (kind paid : Nat) : Resolution :=
  .grant (.mshReflexive kind paid) .source

/-- Nested `sequence` constructors, left to right. An `or` stays one step:
flattening it would resolve every alternative. -/
def flatten : Resolution → List Resolution
  | .sequence rs => rs.flatMap flatten
  | r => [r]

end Resolution

/-- What a spell, activated ability, or trigger does to a permanent (CR 608.2b).
Defined as a type alias for `Resolution` (targeting `.target` by default). -/
def PermanentAction : Type := Resolution
deriving Repr, Inhabited, BEq

namespace PermanentAction

/-- Until-end-of-turn +P/+T. -/
def pump (power toughness : Int) : PermanentAction :=
  Resolution.pump (.fixed power) (.fixed toughness) .target

/-- Until-end-of-turn +P/+T and trample. -/
def pumpAndTrample (power toughness : Int) : PermanentAction :=
  Resolution.sequence [.pump (.fixed power) (.fixed toughness) .target, .grant (.keywords Keyword.trample) .target]

/-- Destroy the permanent (CR 701.7). -/
def destroy : PermanentAction :=
  Resolution.destroy .target

/-- Put `n` +1/+1 counters on the permanent (CR 122.1). -/
def plusOne (n : Nat) : PermanentAction :=
  Resolution.putCounters (.ofKind .plusOnePlusOne n) .permanent

/-- Deal `amount` damage. -/
def dealDamage (amount : Nat) : PermanentAction :=
  Resolution.dealDamage (.fixed amount) .target

/-- The permanent loses indestructible until end of turn. -/
def loseIndestructible : PermanentAction :=
  Resolution.lose .indestructible .target

/-- The permanent can't be blocked this turn. -/
def cantBeBlocked : PermanentAction :=
  Resolution.cant (.beBlocked .target)

/-- Grant these keywords until end of turn. -/
def grantKeywords (k : Keywords) : PermanentAction :=
  Resolution.grant (.keywords k) .target

/-- Put an indestructible counter on the permanent. -/
def indestructibleCounter : PermanentAction :=
  Resolution.putCounters (.ofKind .indestructible) .permanent

/-- Put a double strike counter on the permanent. -/
def doubleStrikeCounter : PermanentAction :=
  Resolution.putCounters (.ofKind .doubleStrike) .permanent

/-- Put a burden counter on the permanent. -/
def burdenCounter : PermanentAction :=
  Resolution.putCounters (.ofKind .burden) .permanent

/-- Tap the permanent. -/
def tap : PermanentAction :=
  Resolution.tap .target

/-- Untap the permanent. -/
def untap : PermanentAction :=
  Resolution.untap .target

/-- Until end of turn, this becomes an artifact in addition to its other
types and gains indestructible. -/
def becomeArtifactIndestructible : PermanentAction :=
  Resolution.sequence [.becomeArtifact .target, .grant (.keywords Keyword.indestructible) .target]

/-- The permanent becomes prepared (Reality Fracture). -/
def becomePrepared : PermanentAction :=
  Resolution.becomePrepared .target

/-- Until-end-of-turn layer-7b base power and toughness (CR 613.4b). -/
def setBasePT (power toughness : Int) : PermanentAction :=
  Resolution.setBasePT (.fixed power) (.fixed toughness) .target

/-- Tap the permanent and put a stun counter on it (CR 122.1d). -/
def tapAndStun : PermanentAction :=
  Resolution.sequence [.tap .target, .putCounters (.ofKind .stun) .permanent]

/-- The owner puts this permanent on top of their library. -/
def putOnTopOfLibrary : PermanentAction :=
  Resolution.putOnLibrary .top .target

/-- The owner puts this permanent on the bottom of their library. -/
def putOnBottomOfLibrary : PermanentAction :=
  Resolution.putOnLibrary .bottom .target

/-- Exile the permanent. -/
def exile : PermanentAction :=
  Resolution.exile .target .forLater

/-- Until end of turn, add this permanent's power and toughness to itself,
which doubles them. -/
def doublePowerAndToughness : PermanentAction :=
  Resolution.pump .double .double .target

/-- Oracle-style text for this action on `noun` (e.g. `target creature`).
`sentence` capitalizes the first letter for activated-ability lines. -/
def toNotation (action : PermanentAction) (noun : String) (sentence := false) : String :=
  let damage (n : Nat) : String := s!"deals {n} damage to {noun}"
  let r : Resolution := action
  let raw :=
    match r with
    | .pump (.fixed p) (.fixed t) _ =>
      s!"{noun} gets {signedStat p}/{signedStat t} until end of turn"
    | .sequence [.pump (.fixed p) (.fixed t) _, .grant (.keywords k) _] =>
      if k == Keyword.trample then
        s!"{noun} gets {signedStat p}/{signedStat t} and gains trample until end of turn"
      else ""
    | .destroy _ .none => s!"destroy {noun}"
    | .putCounters (.ofKind .plusOnePlusOne n) _ => s!"put {plusOnePlusOneCountersPhrase n} on {noun}"
    | .dealDamage (.fixed n) _ .none => damage n.toNat
    | .lose .indestructible _ =>
      s!"{noun} loses indestructible until end of turn"
    | .cant (.beBlocked _) => s!"{noun} can't be blocked this turn"
    | .grant (.keywords k) _ =>
      s!"{noun} gains {k.joinedAnd} until end of turn"
    | .putCounters (.ofKind .indestructible 1) _ =>
      s!"put an indestructible counter on {noun}"
    | .putCounters (.ofKind .doubleStrike 1) _ =>
      s!"put a double strike counter on {noun}"
    | .putCounters (.ofKind .burden 1) _ =>
      s!"put a burden counter on {noun}"
    | .tap _ true => s!"tap {noun}"
    | .untap _ => s!"untap {noun}"
    | .sequence [.becomeArtifact _, .grant (.keywords k) _] =>
      if k == Keyword.indestructible then
        s!"until end of turn, {noun} becomes an artifact in addition to its other types and gains indestructible"
      else ""
    | .becomePrepared _ true => s!"{noun} becomes prepared"
    | .setBasePT (.fixed p) (.fixed t) _ =>
      s!"{noun} has base power and toughness {p}/{t} until end of turn"
    | .sequence [.tap _ true, .putCounters (.ofKind .stun 1) _] =>
      s!"tap {noun} and put a stun counter on it"
    | .putOnLibrary .top _ =>
      s!"{noun}'s owner puts it on top of their library"
    | .putOnLibrary .bottom _ =>
      s!"{noun}'s owner puts it on the bottom of their library"
    | .exile _ .forLater .none => s!"exile {noun}"
    | .pump .double .double _ =>
      s!"double {noun}'s power and toughness until end of turn"
    | _ => ""
  if sentence then capitalizeAscii raw else raw

end PermanentAction

namespace Resolution

/-- What `action` does to `who`. `target` is the announced permanent. -/
def ofAffected (who : ObjectSelector) (action : PermanentAction) : Resolution :=
  let r : Resolution := action
  match r with
  | .putCounters what _ => .putCounters what (counterWho who)
  | .pump p t _ => .pump p t who
  | .sequence [.pump p t _, .grant what _] =>
    .sequence [.pump p t who, .grant what who]
  | .destroy _ note => .destroy who note
  | .dealDamage n _ note => .dealDamage n who note
  | .lose what _ => .lose what who
  | .cant (.beBlocked _) => .cant (.beBlocked who)
  | .sequence [.becomeArtifact _, .grant what _] =>
    .sequence [.becomeArtifact who, .grant what who]
  | .becomePrepared _ prep => .becomePrepared who prep
  | .setBasePT p t _ => .setBasePT p t who
  | .grant what _ => .grant what who
  | .tap _ true => .tap (tapWho who) true
  | .untap _ => .untap who
  | .sequence [.tap _ true, .putCounters what _] =>
    .sequence [.tap (tapWho who), .putCounters what (counterWho who)]
  | .putOnLibrary place _ => .putOnLibrary place who
  | .exile _ how note => .exile who how note
  | r => r
where
  counterWho : ObjectSelector → ObjectSelector
    | .any | .target .any => .permanent
    | w => w
  tapWho : ObjectSelector → ObjectSelector
    | .enchanted => .enchantedWhileSource
    | w => w

/-- Affect a still-legal permanent (by default `.target`, or `.source` if the
source is still on the battlefield). -/
def onPermanent (action : PermanentAction) (who : ObjectSelector := .target) : Resolution :=
  ofAffected who action

/-- Affect the source if it is still on the battlefield. -/
def onSource (action : PermanentAction) : Resolution :=
  ofAffected .source action

/-- What `action` does to the announced permanent. -/
def ofPermanent : PermanentAction → Resolution :=
  ofAffected .target

/-- What `action` does to the source if it is still on the battlefield. -/
def ofSource : PermanentAction → Resolution :=
  ofAffected .source

/-- What `action` does to the creature this Aura enchants. -/
def ofEnchanted : PermanentAction → Resolution :=
  ofAffected .enchanted

/-- What `action` does to the target while the source is still on the battlefield.
A source that already left is silent. -/
def ofTargetWhileSource : PermanentAction → Resolution :=
  ofAffected (.target .whileSource)

/-- The `PermanentAction` that `ofAffected who` built for `r`, if any. -/
def affectedAction? (who : ObjectSelector) (r : Resolution) : Option PermanentAction :=
  let cWho := match who with | .any | .target .any => .permanent | w => w
  let tWho := match who with | .enchanted => .enchantedWhileSource | w => w
  match r with
  | .putCounters (.ofKind .plusOnePlusOne n) w => if w == cWho then some (.plusOne n) else none
  | .pump (.fixed p) (.fixed t) w => if w == who then some (.pump p t) else none
  | .sequence [.pump (.fixed p) (.fixed t) w1, .grant (.keywords k) w2] =>
    if w1 == who && w2 == who && k == Keyword.trample then some (.pumpAndTrample p t) else none
  | .destroy w .none => if w == who then some .destroy else none
  | .dealDamage (.fixed n) w .none => if w == who then some (.dealDamage n.toNat) else none
  | .grant (.keywords k) w => if w == who then some (.grantKeywords k) else none
  | .tap w true => if w == tWho then some .tap else none
  | .untap w => if w == who then some .untap else none
  | .lose .indestructible w => if w == who then some .loseIndestructible else none
  | .cant (.beBlocked w) => if w == who then some .cantBeBlocked else none
  | .putCounters (.ofKind .indestructible 1) w => if w == cWho then some .indestructibleCounter else none
  | .putCounters (.ofKind .doubleStrike 1) w => if w == cWho then some .doubleStrikeCounter else none
  | .putCounters (.ofKind .burden 1) w => if w == cWho then some .burdenCounter else none
  | .sequence [.becomeArtifact w1, .grant (.keywords k) w2] =>
    if w1 == who && w2 == who && k == Keyword.indestructible then some .becomeArtifactIndestructible else none
  | .becomePrepared w true => if w == who then some .becomePrepared else none
  | .setBasePT (.fixed p) (.fixed t) w => if w == who then some (.setBasePT p t) else none
  | .sequence [.tap w1 true, .putCounters (.ofKind .stun 1) w2] =>
    if w1 == tWho && w2 == cWho then some .tapAndStun else none
  | .putOnLibrary .top w => if w == who then some .putOnTopOfLibrary else none
  | .putOnLibrary .bottom w => if w == who then some .putOnBottomOfLibrary else none
  | .exile w .forLater .none => if w == who then some .exile else none
  | .pump .double .double w => if w == who then some .doublePowerAndToughness else none
  | _ => none

/-- The `PermanentAction` that `onPermanent` built for `r`, if any. -/
def onPermanent? : Resolution → Option PermanentAction :=
  affectedAction? .target

/-- The `PermanentAction` that `onSource` built for `r`, if any. -/
def onSource? : Resolution → Option PermanentAction :=
  affectedAction? .source

end Resolution

namespace TriggeredAbility

abbrev TriggerResolution := Resolution

namespace TriggerResolution

export Resolution (
  pump
  dealDamage
  putCounters
  queueReflexive
  sequence
  may
  exile
  put
  chooseModes
  grant
  revealLibrary
  searchLibrary
  attach
  «if»
  connive
  fight
  unlessPays
  cascade
  ringTempts
  additionalCombatPhase
  winTheGame
  counter
  scry
  mill
  draw
  gainLife
  tap
  discard
  pay
  addMana
  returnToHand
  putOnLibrary
  sacrifice
  destroy
  amass
  createTokens
  mayCast
  unrecognized
  ofAffected
  ofPermanent
  ofSource
  ofEnchanted
  ofTargetWhileSource
  onPermanent
  onSource
  lose
  cant
  becomeArtifact
  becomePrepared
  setBasePT
  removeCounters
  untap
  recruit
  gainControl
  noteResolveThisTurn
  ifElse
  or
  spellsCostLess
  revealFromHand
  surveil
  empowerJace
  loseLife
  becomeCopy
  replace
  investigate
  proliferate
  mshReflexive
)

/-- What `queueReflexive` does with a follow-up resolution.
`.modeled` queues that MSH reflexive. `times` is how many times a mana
cost may be paid. `.counters` reads the source's +1/+1 counters as the
paid count. `.damage` deals that much to any target. `.copy` exiles and
copies a milled spell. `.divided` deals that total among one or two
targets. `.attackPump` arms this turn's attack pump. `.none` queues
nothing. -/
inductive QueuedReflexive where
  /-- Queued reflexive action kind (`modeled`, `counters`, `damage`, `copy`, `divided`, `attackPump`, or `none`). -/
  | queuedReflexiveKind (n : Nat := 0) (times : Nat := 0)
      (countersFlag : Bool := false) (damageFlag : Bool := false) (dividedFlag : Bool := false)
      (copyFlag : Bool := false) (attackPumpFlag : Bool := false) (noneFlag : Bool := false)
deriving Repr, Inhabited, BEq

namespace QueuedReflexive

@[match_pattern] abbrev modeled (kind times : Nat) : QueuedReflexive :=
  .queuedReflexiveKind kind times false false false false false false
@[match_pattern] abbrev counters (kind : Nat) : QueuedReflexive :=
  .queuedReflexiveKind kind 0 true false false false false false
@[match_pattern] abbrev damage (n : Nat) : QueuedReflexive :=
  .queuedReflexiveKind n 0 false true false false false false
@[match_pattern] abbrev divided (amount : Nat) : QueuedReflexive :=
  .queuedReflexiveKind amount 0 false false true false false false
@[match_pattern] abbrev copy : QueuedReflexive :=
  .queuedReflexiveKind 0 0 false false false true false false
@[match_pattern] abbrev attackPump : QueuedReflexive :=
  .queuedReflexiveKind 0 0 false false false false true false
@[match_pattern] abbrev none : QueuedReflexive :=
  .queuedReflexiveKind 0 0 false false false false false true

end QueuedReflexive

/-- Trick Arrows: Net, Explosive, and Boomerang.
Paying up to three times is
`.chooseModes trickArrowModes .alreadyChosen`. -/
def trickArrowModes : List TriggerResolution :=
  [.cant .beBlocked,
   .dealDamage (.fixed 2) (.player (.target .opponent)),
   .sequence [.discard, .draw (.fixed 1)]]

/-- Which reflexive `follow` queues as a printed MSH ability. Any other
resolution is `.none`; the caller still puts that follow-up on the stack. -/
def queuedReflexive : TriggerResolution → QueuedReflexive
  | .grant (.keywords k) .target =>
    if k == Keyword.indestructible then
      .modeled (TriggerReflexiveKind.toNat .grantIndestructible) 1
    else .none
  | .chooseModes modes .alreadyChosen =>
    if modes == trickArrowModes then
      .modeled (TriggerReflexiveKind.toNat .trickArrows) modes.length
    else .none
  | .putCounters (.ofKind .indestructible _) .permanent =>
    .modeled (TriggerReflexiveKind.toNat .indestructibleCounter) 1
  | .gainControl .duringNextTurn =>
    .modeled (TriggerReflexiveKind.toNat .controlOpponent) 1
  | .exile (.opponentTop 5) (.mayCastUpTo 2) _ =>
    .modeled (TriggerReflexiveKind.toNat .exileTopFive) 1
  | .put .creatureCard .tapped (.entering mods) =>
    if mods == [.attacking, .counter .finality] then
      .modeled (TriggerReflexiveKind.toNat .returnAttacking) 1
    else .none
  | .destroy .target .none =>
    .modeled (TriggerReflexiveKind.toNat .destroyOppNonland) 1
  | .cant (.beBlockedExceptByHaste .target) =>
    .modeled (TriggerReflexiveKind.toNat .hasteUnblockable) 1
  | .returnToHand (.graveyardInstants _) .none =>
    .modeled (TriggerReflexiveKind.toNat .returnInstants) 1
  | .putCounters (.ofKind .plusOnePlusOne _) .permanent =>
    .modeled (TriggerReflexiveKind.toNat .plusOne) 1
  | .dealDamage .plusOneCounters .target .none =>
    .counters (TriggerReflexiveKind.toNat .countersDamage)
  | .dealDamage (.fixed n) .target .divided =>
    .divided n.toNat
  | .dealDamage (.fixed n) .target .none =>
    .damage n.toNat
  | .mayCast .milledSpell .causingSpell .withoutPaying _ =>
    .copy
  | .pump .perPlains .perPlains .target =>
    .attackPump
  | _ => .none

export Resolution (flatten)

/-- Add {G}{G}{G}. Put a +1/+1 counter on each creature you control.
Scry 2, then draw a card. -/
def allianceModes : List TriggerResolution :=
  [.addMana #[.colored .green, .colored .green, .colored .green],
   .putCounters (.ofKind .plusOnePlusOne) .youControl,
   .sequence [.scry (.fixed 2), .draw (.fixed 1)]]

/-- Put a +1/+1 counter on the source. Each opponent loses 2 life and you
gain 2 life. Draw a card. -/
def gollumModes : List TriggerResolution :=
  [.putCounters (.ofKind .plusOnePlusOne) .source,
   .sequence [.loseLife (.fixed 2) .eachOpponent, .gainLife (.fixed 2)],
   .draw (.fixed 1)]

/-- Draw a card, then discard a card. Each opponent loses 2 life.
Destroy the announced token. Each player sacrifices the announced creature,
which is already gone when an earlier mode destroyed it. -/
def upToXModes : List TriggerResolution :=
  [.sequence [.draw (.fixed 1), .discard (.cards 1)],
   .loseLife (.fixed 2) .eachOpponent,
   .destroy .target (note := .chosenToken),
   .sacrifice .eachPlayersCreature]

/-- Put a +1/+1 counter on the source. Draw a card after removing a counter
from a creature you control. `.plusOneOrRemoveCounter` asks for the choice
and removes the counter; the draw is that mode's follow-up. -/
def hydeModes : List TriggerResolution :=
  [.putCounters (.ofKind .plusOnePlusOne) .source, .draw (.fixed 1)]

/-- The Vision gains double strike until end of turn. The Vision gains
indestructible until end of turn. Draw a card. `.vision` asks for one that
has not been chosen this turn. -/
def visionModes : List TriggerResolution :=
  [.grant (.keywords Keyword.doubleStrike) .source,
   .grant (.keywords Keyword.indestructible) .source,
   .draw (.fixed 1)]

/-- A spell step as the same step in this vocabulary. -/
def ofSpell (r : TriggerResolution) : TriggerResolution := r

end TriggerResolution

end TriggeredAbility

/-- How a spell resolves (CR 608). The same inductive as a trigger resolution. -/
abbrev SpellResolution := Resolution

namespace SpellResolution

-- Constructors stay addressable as `SpellResolution.draw` and the rest.
export Resolution (
  pump
  dealDamage
  scry
  draw
  searchLibrary
  discard
  pay
  putCounters
  returnToHand
  queueReflexive
  sacrifice
  lose
  cant
  becomeArtifact
  becomePrepared
  setBasePT
  putOnLibrary
  sequence
  may
  gainLife
  exile
  put
  removeCounters
  tap
  untap
  destroy
  recruit
  amass
  createTokens
  attach
  addMana
  gainControl
  cascade
  noteResolveThisTurn
  «if»
  ifElse
  or
  chooseModes
  mayCast
  grant
  revealLibrary
  mill
  ringTempts
  spellsCostLess
  investigate
  proliferate
  mshReflexive
  connive
  fight
  revealFromHand
  surveil
  empowerJace
  additionalCombatPhase
  loseLife
  winTheGame
  becomeCopy
  onPermanent
  onSource
  counter
  unlessPays
  replace
  unrecognized
)


/-- The “if …” clause for `cond`, without a following resolution. -/
private def ifClause (cond : TriggeredAbility.ConditionSelector) (noun : String) : String :=
  match cond with
  | .subtype subtype => s!"if {noun} is {indefinite subtype} {subtype}"
  | .mvAtMost n => s!"if that spell's mana value was {n} or less"
  | .castFromGraveyard => "if this spell was cast from a graveyard"
  | .notFromHand => "if this spell wasn't cast from your hand"
  | .teamwork => "if this spell was cast using teamwork"
  | .giftPromised => "if the gift was promised"
  | _ => "if that is true"

/-- Drop one trailing period so a following clause can continue the sentence. -/
private def trimPeriod (s : String) : String :=
  if s.endsWith "." then (s.dropEnd 1).toString else s

private def phraseOneFallback (r : SpellResolution) (noun : String) : String :=
  match r.onPermanent? with
  | some action => PermanentAction.toNotation action noun
  | none => ""

private def phraseOneCombat (r : SpellResolution) (noun : String) : String :=
  match r with
  | .pump (.fixed p) (.fixed t) .creaturesYouControl =>
    s!"creatures you control get {signedStat p}/{signedStat t} until end of turn"
  | .pump (.fixed p) (.fixed t) .allCreatures =>
    s!"all creatures get {signedStat p}/{signedStat t} until end of turn"
  | .pump (.fixed p) (.fixed t) .creaturesOfTargetPlayer =>
    s!"creatures {noun} controls get {signedStat p}/{signedStat t} until end of turn"
  | .pump (.fixed p) (.fixed t) .creatureTargets =>
    PermanentAction.toNotation (.pump p t) "target creature"
  | .dealDamage .otherSpellsManaValue .opponentsCreatures _ =>
    "deals damage to each creature your opponents control equal to the total mana value of other spells you've cast this turn"
  | .dealDamage (.fixed n) .allCreatures _ =>
    s!"deals {n} damage to each creature"
  | .dealDamage (.fixed n) .opponentsCreatures _ =>
    s!"deals {n} damage to each creature your opponents control"
  | .dealDamage (.fixed n) (.nonSubtypeCreatures subtype) _ =>
    s!"deals {n} damage to each non-{subtype} creature"
  | .dealDamage .otherSpellsManaValue .allCreatures _ =>
    "deals damage to each creature equal to the total mana value of other spells you've cast this turn"
  | .dealDamage .otherSpellsManaValue (.nonSubtypeCreatures subtype) _ =>
    s!"deals damage to each non-{subtype} creature equal to the total mana value of other spells you've cast this turn"
  | .dealDamage (.fixed n) (.player (.controller .target)) _ =>
    s!"it also deals {n} damage to that creature's controller"
  | r => phraseOneFallback r noun

private def phraseOneGrant (r : SpellResolution) (noun : String) : String :=
  match r with
  | .fight _ (.timesPower 1) =>
    "target creature you control deals damage equal to its power to target creature an opponent controls"
  | .fight _ (.timesPower k) =>
    s!"Target creature you control deals damage equal to {timesPhrase k} its power to target creature an opponent controls."
  | .fight .announced .mutual =>
    "target creature you control fights target creature an opponent controls"
  | .fight .announced .upToOneOther =>
    "target creature you control fights up to one other target creature"
  | .grant .extraLand .youIfCast => "you may play an additional land this turn"
  | .grant (.keywords k) .creaturesYouControl =>
    s!"creatures you control gain {k.joinedAnd} until end of turn"
  | .counter => s!"counter {noun}"
  | .attach .equipmentYouControl .target =>
    "attach an Equipment you control to it"
  | .recruit => "recruit"
  | .gainControl .exchangeTargets =>
    "exchange control of two target nonland permanents that share a card type"
  | .replace =>
    s!"if {noun} would die this turn, exile it instead"
  | .cant (.castSpellsThisTurn .any) =>
    "players can't cast spells this turn"
  | .gainControl .oppArtifacts =>
    "for each opponent, gain control of up to one target artifact that player controls"
  | .grant .phaseOutKicker .target =>
    "target creature phases out. If this spell was kicked, each creature target player controls phases out instead"
  | .investigate (.target .player) =>
    "target player investigates"
  | .grant (.keywords k) .creatureTargets =>
    PermanentAction.toNotation (.grantKeywords k) "target creature"
  | .grant (.artifactCreature p t kw) .target =>
    s!"until end of turn, {noun} becomes an artifact creature with base power and toughness {p}/{t} and gains {kw}"
  | .becomeCopy .nontokenCreaturesYouControl =>
    "For each nontoken creature you control, create a token that's a copy of that creature, except it isn't legendary."
  | .gainControl .untilEotOrNextIfVillain =>
    "Gain control of target creature until end of turn. If you control a Villain with greater mana value than that creature, gain control of that creature until the end of your next turn instead. Untap that creature. It gains haste until end of turn."
  | .spellsCostLess (.cardType ty) (.fixed n) =>
    s!"{ty} spells you cast this turn cost \{{n}} less to cast"
  | .spellsCostLess (.supertype s) (.fixed n) =>
    s!"{s} spells you cast this turn cost \{{n}} less to cast"
  | r => phraseOneFallback r noun

private def phraseOnePlayerResource (r : SpellResolution) (noun : String) : String :=
  match r with
  | .unrecognized => "this effect does nothing"
  | .loseLife (.fixed n) .you => s!"lose {n} life"
  | .loseLife (.fixed n) .player => s!"{noun} loses {n} life"
  | .loseLife (.fixed n) (.controller .target) => s!"its controller loses {n} life"
  | .loseLife (.fixed n) .eachOpponent => s!"each opponent loses {n} life"
  | .gainLife (.fixed n) .you => s!"you gain {n} life"
  | .gainLife (.fixed n) .player => s!"Target player gains {n} life"
  | .surveil (.fixed n) .none => s!"surveil {n}"
  | .draw (.fixed n) .you => s!"draw {cardPhrase n.toNat}"
  | .draw (.fixed n) .player => s!"{noun} draws {cardPhrase n.toNat}"
  | .scry (.fixed n) => s!"scry {n}"
  | .addMana #[.colored .red] (.count (.oppPermanents ty)) _ =>
    s!"add {"{R}"} for each {ty.oracleWord} your opponents control"
  | .draw .greatestToughnessThenPutCreatures _ =>
    "draw cards equal to the greatest toughness among creatures you control, then put any number of creature cards from your hand onto the battlefield"
  | .mill (.fixed n) _ (.toHand (.oneOf a b)) =>
    s!"mill {n} cards, then put {indefinite a.oracleWord} {a.oracleWord} or {b.oracleWord} card from among them into your hand"
  | .mill (.fixed n) _ (.toHand (.upTo max ty)) =>
    s!"mill {n} cards, then put up to {englishNumber max} {ty.oracleWord} cards from among them into your hand"
  | .mill (.fixed n) _ (.toHand (.allOf a b)) =>
    s!"mill {n} cards, then put all {a.oracleWord} and {b.oracleWord} cards from among them into your hand"
  | .addMana #[] (.fixed n) (.subtypeSpells subtype) =>
    s!"add {englishNumber n.toNat} mana in any combination of colors. Spend this mana only to cast {subtype} spells"
  | .mill (.fixed n) _ (.permanentAndGainLife life) =>
    s!"Mill {n} cards. You may put a permanent card from among the milled cards into your hand. You gain {life} life."
  | .mayCast .nextRedOrGreenCreature .unlimited .withoutPaying _ =>
    "The next red or green creature spell you cast this turn can be cast without paying its mana cost"
  | r => phraseOneFallback r noun

private def phraseOneTapDiscardOrReturn (r : SpellResolution) (noun : String) : String :=
  match r with
  | .discard (.cards n) => s!"discard {cardPhrase n}"
  | .returnToHand .targetSpell _ => s!"return {noun} to its owner's hand"
  | .returnToHand (.target .graveyardCard) _ => s!"return up to one {noun} to your hand"
  | .tap (.target .eachPermanent) => "tap one or two target creatures"
  | .returnToHand .creaturesNotChosenType _ =>
    "choose a creature type. Return all creatures that aren't of the chosen type to their owners' hands"
  | .returnToHand .ownedCreaturesKicker .delayedBirds =>
    "choose target creature you own. If this spell was kicked, instead choose any number of target creatures you own. Return each chosen creature to your hand. At the beginning of the next upkeep, create a 4/4 white Bird Soldier creature token with flying for each creature returned to your hand this way"
  | .returnToHand .eachPermanent _ =>
    "return one or two target nonland permanents to their owners' hands"
  | .untap .creatureTargets =>
    PermanentAction.toNotation .untap "target creature"
  | .returnToHand (.graveyardSubtype subtype) _ =>
    s!"return target {subtype} card from your graveyard to your hand"
  | .discard (.cardsUnlessType n ty) =>
    s!"discard {englishNumber n} cards unless you discard {indefinite ty.oracleWord} {ty.oracleWord} card"
  | .putOnLibrary .secondOrBottomThenConnive .target =>
    "The owner of target creature an opponent controls puts it into their library second from the top or on the bottom. Then up to one target creature you control connives."
  | .returnToHand .upToTwoGyModal _ =>
    "Choose up to two. Return those cards from your graveyard to your hand. • Target artifact card. • Target creature card. • Target enchantment card. • Target land card."
  | r => phraseOneFallback r noun

private def phraseOneTokensOrCounters (r : SpellResolution) (noun : String) : String :=
  match r with
  | .putCounters (.ofKind kind n) .creatureTargets =>
    s!"put {kind.countersPhrase n} on up to one target creature"
  | .putCounters (.ofKind kind n) .firstTargetCreatureYouControl =>
    s!"put {kind.countersPhrase n} on target creature you control"
  | .amass (.fixed n) subtype =>
    s!"amass {pluralizeName subtype} {n}"
  | .createTokens kind .chosenX _ _ _ =>
    s!"create X {kind.pluralNoun}"
  | .createTokens kind (.perSubtype subtype) _ _ _ =>
    s!"Create a {kind.oracleNoun} for each {subtype} you control"
  | .createTokens .galactus (.fixed 1) false .you .none =>
    "Create Galactus, a legendary 16/16 black Elder Alien creature token with flying, trample, and \"Whenever Galactus attacks, destroy target land.\""
  | .createTokens kind (.fixed n) _ .you _ =>
    TokenKind.createPhrase kind n.toNat
  | .createTokens kind (.fixed n) _ .player _ =>
    s!"{noun} creates {TokenKind.createdTokensPhrase kind n.toNat}"
  | .putCounters (.ofKind .plusOnePlusOne n) (.youControl .eachCreature) =>
    s!"put {plusOnePlusOneCountersPhrase n} on each creature you control"
  | .putCounters (.ofKind .plusOnePlusOne n) .eachOther =>
    s!"put {plusOnePlusOneCountersPhrase n} on each other creature you control"
  | .putCounters (.ofKind .plusOnePlusOne n) (.permanent _) =>
    s!"put {plusOnePlusOneCountersPhrase n} on {noun}"
  | r => phraseOneFallback r noun

private def phraseOnePutExileOrDestroy (r : SpellResolution) (noun : String) : String :=
  match r with
  | .exile (.graveyardCardsOfType ty (.target .player)) .anyManaWhileExiled _ =>
    s!"exile all {ty.oracleWord} cards from target player's graveyard. You may cast spells from among those cards for as long as they remain exiled, and mana of any type can be spent to cast them"
  | .exile .targetSpell .forLater .counteredPermanentMayCast =>
    s!"counter {noun}. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled"
  | .exile .eachPermanent .returnImmediately _ =>
    "exile two target creatures and/or lands you control, then return them to the battlefield under their owner's control"
  | .exile .attackingCreatures .forLater .controllerMaySearchBasic =>
    s!"exile all attacking creatures {noun} controls. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle"
  | .exile (.topN n) (.playIfYouControlSubtype subtype) _ =>
    s!"look at the top {n} cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a {subtype}"
  | .exile .opponentTopX .playForLifeThisTurn _ =>
    "exile the top X cards of target opponent's library. You may play those cards this turn. If you cast a spell this way, pay life equal to its mana value rather than pay its mana cost"
  | .put .creaturesDiedThisTurn .tapped .asFood =>
    "put onto the battlefield under your control all creature cards in your opponents' graveyards that were put there from the battlefield this turn. They are Food artifacts with \"{2}, {T}, Sacrifice this artifact: You gain 3 life.\""
  | .exile (.creatureMvAtMostOrTeamwork n) .forLater (.gainLifeIfTeamwork life) =>
    s!"exile target creature with mana value {n} or less. If this spell was cast using teamwork, instead exile target creature and you gain {life} life"
  | .put (.creatureMvAtMostOrTeamwork n) .asPrinted _ =>
    s!"choose target creature card in your graveyard with mana value {n} or less. If this spell was cast using teamwork, instead choose target creature card in your graveyard. Return the chosen card to the battlefield"
  | .exile (.topN _) .playUntilNextTurn _ =>
    s!"exile the top card of your library. {playThatCardUntilNextTurnPhrase}"
  | .exile .allCreatures .forLater .worldsWithinWorlds =>
    "Exile all creatures. Each player may put any number of creature cards from their hand onto the battlefield. Then put all cards exiled this way into their owners' hands. Exile Worlds Within Worlds."
  | .exile .hand .playUntilNextTurn .thenDrawThree =>
    "Exile all the cards from your hand, then draw that many cards. Until the end of your next turn, you may play cards exiled this way."
  | r => phraseOneFallback r noun

private def phraseOneRevealOrReflexive (r : SpellResolution) (noun : String) : String :=
  match r with
  | .searchLibrary (.returnToHand (.supertypeCard s ty) _) =>
    searchLibraryToHandPhrase s!"a {s.oracleWord} {ty.oracleWord} card"
  | .searchLibrary (.put (.supertypeCard s ty) .tapped _) =>
    s!"its controller may search their library for a {s.oracleWord} {ty.oracleWord} card, put it onto the battlefield tapped, then shuffle"
  | .searchLibrary (.put .artifactCreatureX _ _) =>
    "Search your library and/or graveyard for an artifact creature card with mana value X or less and put it onto the battlefield with X additional +1/+1 counters on it. If X is 4 or greater, it gains haste until end of turn. If you search your library this way, shuffle."
  | .revealLibrary (.top n) (.returnToHand .twoPiles _) _ =>
    s!"look at the top {englishNumber n} cards of your library and separate them into a face-down pile and a face-up pile. An opponent chooses one of the piles. Put that pile into your hand and the other into your graveyard"
  | .revealLibrary (.top n) (.sequence [.put .landsYouControl .tapped _, .gainLife (.fixed life) _]) _ =>
    s!"look at the top {n} cards of your library, put any number of land cards from among them onto the battlefield tapped, then shuffle. You gain {life} life"
  | .revealLibrary (.top n) (.put .creaturesYouControl _ _) _ =>
    s!"reveal the top {n} cards of your library. You may put a creature card from among them onto the battlefield. If this spell was cast using teamwork, put any number of creature cards from among them onto the battlefield instead. Put the rest into your graveyard"
  | r => phraseOneFallback r noun

private def phraseOneMay (action follow : SpellResolution) (when : TriggerMayWhen)
    (noun : String) (recurse : SpellResolution → String → String) : String :=
  match action, follow, when with
  | .draw (.perControlled ty) _, .draw (.fixed 1) .eachOpponent, .ifYouDo =>
    s!"You may draw a card for each {ty.oracleWord} you control. If you do, each opponent draws a card"
  | .put (.creatureFromHand subtype n) _ _, .draw (.fixed 1) _, .ifYouDont =>
    s!"You may put {indefinite subtype} {subtype} creature card with mana value {n} or less from your hand onto the battlefield. If you don't, draw a card"
  | .pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card]), .draw (.fixed cards) _, .ifYouDo =>
    s!"You may sacrifice an artifact or discard a card. If you do, draw {cardPhrase cards.toNat}."
  | r, _, _ =>
    let base := recurse r noun
    let base := if base.endsWith "." then (base.dropEnd 1).toString else base
    let base := if base.startsWith "you " then (base.drop 4).toString else base
    if base.isEmpty then "you may" else s!"you may {base}"

private def phraseOneModes (r : SpellResolution) (noun : String)
    (recurse : SpellResolution → String → String) : String :=
  match r with
  | .sequence _ | .or _ => ""
  | .unlessPays r n =>
    let base := recurse r noun
    let base := if base.endsWith "." then (base.dropEnd 1).toString else base
    if base.isEmpty then s!"unless its controller pays \{{n}}"
    else s!"{base} unless its controller pays \{{n}}"
  | .«if» cond r =>
    let base := trimPeriod (recurse r noun)
    let cond := ifClause cond noun
    if base.isEmpty then cond else s!"{cond}, {base}"
  | .ifElse .teamwork (.dealDamage (.fixed teamworkN) .target .none) (.dealDamage (.fixed n) .target .none) =>
    s!"deals {n} damage to target attacking or blocking creature. If this spell was cast using teamwork, it deals {teamworkN} damage to that creature instead"
  | .ifElse .teamwork (.unlessPays .counter teamworkN) (.unlessPays .counter n) =>
    s!"counter target spell unless its controller pays \{{n}}. Counter that spell unless its controller pays \{{teamworkN}} instead if this spell was cast using teamwork"
  | .ifElse cond whenTrue whenFalse =>
    let no := trimPeriod (recurse whenFalse noun)
    let yes := trimPeriod (recurse whenTrue noun)
    let cond := ifClause cond noun
    if no.isEmpty then
      if yes.isEmpty then cond else s!"{cond}, {yes}"
    else if yes.isEmpty then no
    else s!"{no}. {capitalizeAscii cond}, {yes} instead"
  | r => phraseOneFallback r noun

/-- One step, not a sequence or a choice. Sequence and `or` phrasing stay
outside this match so the constructor splitter is not recursive. -/
private partial def phraseOne (r : SpellResolution) (noun : String) : String :=
  match r with
  | .combatCountersOrTokens (some _) .. => phraseOneGrant r noun
  | .combatCountersOrTokens none (some _) ..
  | .combatCountersOrTokens none none none none none .. => phraseOneCombat r noun
  | .combatCountersOrTokens .. => phraseOneTokensOrCounters r noun
  | .playerResource .. => phraseOnePlayerResource r noun
  | .zoneOrTap true .. => phraseOneTapDiscardOrReturn r noun
  | .zoneOrTap false .. => phraseOnePutExileOrDestroy r noun
  | .flowOrReveal true .. | .flowOrReveal false none (some _) .. => phraseOneRevealOrReflexive r noun
  | .may action follow when => phraseOneMay action follow when noun phraseOne
  | .flowOrReveal false (some _) .. => phraseOneFallback r noun
  | .flowOrReveal false none none .. => phraseOneModes r noun phraseOne

export Resolution (flatten)

private def phraseSequencePart2 (rs : List SpellResolution) (noun : String) : String :=
  match rs with
  | [.putCounters (.ofKind kind k) .firstTargetCreatureYouControl, .fight .announced .mutual] =>
    s!"put {kind.countersPhrase k} on target creature you control. Then it fights target creature an opponent controls"
  | [.putCounters (.ofKind kind k) .firstTargetCreatureYouControl,
     .«if» .castFromGraveyard (.putCounters (.ofKind .plusOnePlusOne m) .eachOther)] =>
    s!"put {kind.countersPhrase k} on target creature you control. If this spell was cast from a graveyard, also put {plusOnePlusOneCountersPhrase m} on each other creature you control"
  | [.dealDamage (.fixed n) (.nonSubtypeCreatures sub) _, .addMana #[] (.fixed m) (.subtypeSpells sub2)] =>
    s!"deals {n} damage to each non-{sub} creature. Add {englishNumber m.toNat} mana in any combination of colors. Spend this mana only to cast {sub2} spells"
  | [.returnToHand .targetSpell _, .«if» .giftPromised (.cant (.castSpellsThisTurn .any))] =>
    "return target spell to its owner's hand. If the gift was promised, players can't cast spells this turn"
  | [.dealDamage (.fixed n) .target .none, .«if» .teamwork (.dealDamage (.fixed extra) (.player (.controller .target)) _)] =>
    s!"deals {n} damage to target creature. If this spell was cast using teamwork, it also deals {extra} damage to that creature's controller"
  | [.grant (.keywords k) .target, .«if» .teamwork (.grant (.keywords kw) .target)] =>
    if k == Keyword.doubleStrike then
      s!"target creature gains double strike until end of turn. If this spell was cast using teamwork, that creature also gains {kw.joinedAnd} until end of turn"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | [.investigate (.target .player),
     .grant (.keywords k) .creatureTargets,
     .untap .creatureTargets,
     .pump (.fixed 1) (.fixed 0) .creatureTargets] =>
    if k == Keyword.flying then
      "target player investigates. Target creature gets +1/+0 and gains flying until end of turn. Untap it"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | [.putCounters (.ofKind kind k) .creatureTargets, .gainLife (.fixed n) .player] =>
    s!"put {kind.countersPhrase k} on up to one target creature. Target player gains {n} life"
  | [.destroy .target .none, .searchLibrary (.put (.supertypeCard s ty) .tapped _)] =>
    s!"destroy {noun}. Its controller may search their library for a {s.oracleWord} {ty.oracleWord} card, put it onto the battlefield tapped, then shuffle"
  | [.draw (.fixed 3), .discard (.cardsUnlessType n ty)] =>
    s!"draw three cards. Then discard {englishNumber n} cards unless you discard {indefinite ty.oracleWord} {ty.oracleWord} card"
  | [.replace, .dealDamage (.fixed n) .target .none] =>
    s!"deals {n} damage to {noun}. If that creature would die this turn, exile it instead"
  | [.pump (.fixed p) (.fixed t) .target, .replace] =>
    s!"{noun} gets {signedStat p}/{signedStat t} until end of turn. If that creature would die this turn, exile it instead"
  | [.dealDamage (.fixed n) .target .none, .lose .indestructible .target, .replace] =>
    s!"deals {n} damage to {noun}. That creature loses indestructible until end of turn. If that creature would die this turn, exile it instead"
  | [.pump (.fixed p) (.fixed t) .target, .exile (.topN 1) .playUntilNextTurn _] =>
    s!"Target creature gets {signedStat p}/{signedStat t} until end of turn.\nExile the top card of your library. {playThatCardUntilNextTurnPhrase}."
  | [.pump .double .double .target, .grant (.keywords k) .target] =>
    if k == Keyword.trample then
      "Choose target creature you control. Until end of turn, double its power and toughness and it gains trample"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | [.gainLife (.fixed life) .player, .searchLibrary (.put .basicLand .asPrinted _), .putCounters (.ofKind .plusOnePlusOne 1) .target] =>
    s!"Target player gains {life} life, then searches their library for a basic land card, puts it onto the battlefield tapped, then shuffles. Put a +1/+1 counter on up to one target creature."
  | [.becomeCopy .sourceSpellXTimes, .dealDamage (.fixed n) .target .none] =>
    s!"When you cast this spell, copy it X times. You may choose new targets for the copies.\ndeals {n} damage to target creature."
  | _ =>
    String.intercalate ". " (rs.map (phraseOne · noun))

/-- Printed wording of a flat sequence. Known shapes keep their Oracle text;
other sequences join each step. -/
private def phraseSequence (rs : List SpellResolution) (noun : String) : String :=
  match (Resolution.sequence rs).onPermanent? with
  | some action => PermanentAction.toNotation action noun
  | none =>
  match rs with
  | [.draw (.fixed n) .you, .discard (.cards 1)] =>
    s!"draw {cardPhrase n.toNat}, then discard a card"
  | [.draw (.fixed cards) .you, .loseLife (.fixed life) .you] =>
    s!"you draw {cardPhrase cards.toNat} and lose {life} life"
  | [.draw (.fixed cards) .player, .loseLife (.fixed life) .player] =>
    s!"{noun} draws {cardPhrase cards.toNat} and loses {life} life"
  | [.destroy .target .none, .loseLife (.fixed n) (.controller .target)] =>
    s!"destroy {noun}. Its controller loses {n} life"
  | [.returnToHand .targetSpell _, .draw (.fixed 1)] =>
    s!"return {noun} to its owner's hand. Draw a card"
  | [.counter, .«if» (.mvAtMost n) .recruit] =>
    s!"counter {noun}. If that spell's mana value was {n} or less, recruit"
  | [.returnToHand (.target .graveyardCard) _, .amass (.fixed n) subtype] =>
    s!"return up to one {noun} to your hand. Amass {pluralizeName subtype} {n}"
  | [.draw (.fixed 1), .loseLife (.fixed 1), .amass (.fixed n) subtype] =>
    s!"you draw a card and lose 1 life. Amass {pluralizeName subtype} {n}"
  | [.createTokens kind (.fixed n) _ .you _, .pump (.fixed p) (.fixed t) .creaturesYouControl] =>
    let tokens := capitalizeAscii (TokenKind.createPhrase kind n.toNat)
    s!"{tokens}, then creatures you control get {signedStat p}/{signedStat t} until end of turn."
  | [.destroy .target .none, .gainLife (.fixed n) .you] =>
    s!"destroy {noun}. You gain {n} life"
  | [.destroy .target .none, .surveil (.fixed 1) .none] =>
    s!"destroy {noun}. Surveil 1"
  | [.tap .target true, .scry (.fixed scryN), .draw (.fixed drawN)] =>
    s!"tap {noun}. Scry {scryN}. Draw {cardPhrase drawN.toNat}"
  | [.pump (.fixed p) (.fixed t) .target, .draw (.fixed 1)] =>
    let tStr := if t == 0 && p < 0 then "-0" else signedStat t
    s!"Target creature gets {signedStat p}/{tStr} until end of turn.\nDraw a card."
  | [.putCounters (.ofKind .plusOnePlusOne 1) .permanent, .grant (.keywords k) .target] =>
    if k == Keyword.lifelink.merge Keyword.indestructible then
      "put a +1/+1 counter on target creature. It gains lifelink and indestructible until end of turn"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | [.grant (.keywords k) .target, .draw (.fixed 1)] =>
    if k == Keyword.vigilance.merge Keyword.cantBeBlocked then
      s!"{noun} gains vigilance until end of turn and can't be blocked this turn"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | [.pump (.fixed p) (.fixed t) .creaturesYouControl, .grant (.keywords k) .creaturesYouControl] =>
    s!"Creatures you control get {signedStat p}/{signedStat t} and gain {k.joinedAnd} until end of turn"
  | [.untap .target, .pump (.fixed p) (.fixed t) .target, .«if» (.subtype subtype) (.may (.attach .equipmentYouControl .target) (.sequence []))] =>
    s!"untap {noun}. It gets {signedStat p}/{signedStat t} until end of turn. If it's {indefinite subtype} {subtype}, you may attach an Equipment you control to it"
  | _ =>
    phraseSequencePart2 rs noun

/-- Printed wording of a choice. The library pair keeps its Oracle sentence;
other choices join each alternative. -/
private def phraseOr (rs : List SpellResolution) (noun : String) : String :=
  match rs with
  | [.putOnLibrary .top .target, .putOnLibrary .bottom .target] =>
    s!"{noun}'s owner puts it on their choice of the top or bottom of their library"
  | [.putOnLibrary .bottom .target, .putOnLibrary .top .target] =>
    s!"{noun}'s owner puts it on their choice of the top or bottom of their library"
  | _ =>
    String.intercalate " or " ((rs.map (phraseOne · noun)).filter (· != ""))

/-- Oracle-style reminder from targeting and resolution. `.fight` with
`.timesPower` is the one-sided Quarrel wording, including a multiple of that
power. `.fight .announced` is the two-creature fight, including the later step
of a counter-then-fight sequence and a fight of up to one other creature. -/
def toPhrase (r : SpellResolution) (noun : String) : String :=
  match r with
  | .sequence rs => phraseSequence (rs.flatMap flatten) noun
  | .or rs => phraseOr rs noun
  | r => phraseOne r noun

end SpellResolution

end Mtg.Engine
