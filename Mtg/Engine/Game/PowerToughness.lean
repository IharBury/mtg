import Mtg.Engine.Game.Attachments

/-!
# Current power, toughness, and subtypes (CR 613.1d / 613.4)

Characteristic-defining abilities (layer 7a, CR 604.3 / 613.4a), base P/T
setting effects (layer 7b, CR 613.4b), continuous stat bonuses from lords,
Auras, Equipment, and count-based effects (layer 7c, CR 613.4c), counters
and pumps (CR 613.4c), subtype queries (CR 205.3m / 613.1d), and final
power and toughness queries (CR 208.2).
-/

namespace Mtg.Engine
namespace Game

/-- Mana value of other spells `p` has cast this turn. Copies that were not
cast are not recorded. -/
def otherCastManaValueThisTurn (g : Game) (p : PlayerId) : Nat :=
  (g.player p).castManaValuesThisTurn.foldl (· + ·) 0

/-- Lands `p` currently controls (CR 305.1). -/
def landsYouControl (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).filter (·.printed.isLand) |>.size

/-- Whether `o` currently has a “P/T equal to lands you control” ability.
This characteristic-defining ability functions in all zones (CR 208.2a / 604.3). -/
def hasLandsYouControlPT (_g : Game) (o : GameObject) : Bool :=
  o.staticAbilities.any StaticAbility.isLandsYouControlPT

/-- Layer-7b “power becomes the number of cards in your hand” (Ms. Marvel).
This overwrites an earlier effect that set power (ruling 640). -/
def hasHandSizeSetPower (o : GameObject) : Bool :=
  o.status.cardsInHandPowerUntilEot ||
    o.status.grantedStaticAbilities.any StaticAbility.isCardsInHandPower

/-- Number of card types among cards in all graveyards (Tarmogoyf). Card
types, not cards, are counted, and supertypes are not card types (rulings
797 / 800). -/
def graveyardCardTypeCount (g : Game) : Nat :=
  let types := g.objects.foldl (fun acc o =>
    match o.zone with
    | .graveyard _ => o.printed.types.foldl (fun acc t =>
        if acc.contains t then acc else acc.push t) acc
    | _ => acc) (#[] : Array CardType)
  types.size

/-- Basic land types among lands `p` controls (domain; CR 305.6). -/
def basicLandTypesAmong (g : Game) (p : PlayerId) : Nat :=
  (#["Plains", "Island", "Swamp", "Mountain", "Forest"].filter (fun t =>
    (g.permanentsOf p).any (fun o => o.printed.isLand && o.hasSubtype t))).size

/-- Layer-7a characteristic-defining power and/or toughness (CR 604.3 / 613.4a).
Functions in all zones and may be overwritten on the battlefield by a Layer-7b
base P/T setting effect. -/
def cdaValues (g : Game) (o : GameObject) : Option Int × Option Int :=
  o.staticAbilities.foldl (fun (accP, accT) ab =>
    match ab with
    | .cda which =>
      match which with
      | .powerToughnessEqualLandsYouControl =>
        let n : Int := Int.ofNat (g.landsYouControl o.you)
        (accP.orElse (fun _ => some n), accT.orElse (fun _ => some n))
      | .ptEqualGraveyardCardTypes =>
        let n : Int := Int.ofNat g.graveyardCardTypeCount
        (some n, some (n + 1))
      | .powerEqualCardsInHand =>
        if o.printed.staticAbilities.any StaticAbility.isCardsInHandPower then
          (some (Int.ofNat (g.player o.you).hand.size), accT)
        else (accP, accT)
      | .powerEqualCreaturesYouControl =>
        (some (Int.ofNat (g.countCreaturesControlledBy o.you)), accT)
      | .powerEqualSubtypeYouControl subtype =>
        let n : Int := Int.ofNat ((g.permanentsOf o.you).filter (·.hasSubtype subtype) |>.size)
        (some n, accT)
      | .powerEqualLegendaryCreaturesYouControl =>
        let n : Int := Int.ofNat ((g.permanentsOf o.you).filter (fun p =>
          p.isCreature && p.isLegendary) |>.size)
        (some n, accT)
      | .powerEqualsBasicLandTypes =>
        (some (Int.ofNat (g.basicLandTypesAmong o.you)), accT)
    | _ => (accP, accT)) (none, none)

def characteristicBasePT (g : Game) (o : GameObject) : Int × Int :=
  if o.status.faceDown then (2, 2)
  else if o.isOnBattlefield && o.status.animatedConstruct55 then
    (o.status.setBasePower.getD 5, o.status.setBaseToughness.getD 5)
  else
    let (cdaP, cdaT) := g.cdaValues o
    let baseP := cdaP.getD (o.printed.power.getD 0)
    let baseT := cdaT.getD (o.printed.toughness.getD 0)
    let power :=
      if hasHandSizeSetPower o then
        -- Ms. Marvel (ruling 640): this layer-7b set overwrites earlier sets.
        Int.ofNat (g.player o.you).hand.size
      else if o.isOnBattlefield then
        o.status.setBasePower.getD baseP
      else baseP
    let toughness :=
      if o.isOnBattlefield then o.status.setBaseToughness.getD baseT else baseT
    (power, toughness)

/-- Characteristic power before pumps, counters, and attached bonuses. -/
def characteristicBasePower (g : Game) (o : GameObject) : Int :=
  (g.characteristicBasePT o).1

/-- Characteristic toughness before pumps, counters, and attached bonuses. -/
def characteristicBaseToughness (g : Game) (o : GameObject) : Int :=
  (g.characteristicBasePT o).2

/-- Componentwise sum of two power/toughness bonuses. -/
def addStats (a b : Int × Int) : Int × Int :=
  (a.1 + b.1, a.2 + b.2)

/-- True when `src` is a lord that can grant an ability to `target` (CR 604.2). -/
def isLordOf (src target : GameObject) : Bool :=
  src.id != target.id &&
  src.isOnBattlefield &&
  target.isOnBattlefield &&
  src.controller == target.controller &&
  src.controller.isSome &&
  target.isCreature

/-- Current subtypes after Aura type-setting (e.g. Fog on the Barrow-Downs
makes the enchanted creature only a Spirit; CR 205.3m / 613.1d). -/
def currentSubtypes (g : Game) (o : GameObject) : Array Subtype :=
  match g.battlefield.find? (fun a =>
    a.attachedTo == some o.id &&
      a.staticAbilities.any (fun ab => ab.enchantedOnlySubtype?.isSome)) with
  | none => o.subtypes
  | some aura =>
    match aura.staticAbilities.findSome? (fun ab => ab.enchantedOnlySubtype?) with
    | some s => #[s]
    | none => o.subtypes

/-- Creature cards in `p`'s graveyard. -/
def gyCreatureCards (g : Game) (p : PlayerId) : Nat :=
  (g.player p).graveyard.filter (fun id =>
    (g.findObject? id).any (·.printed.isCreature)) |>.size

/-- Undercover Skrull: all creature types while enough creature cards are
in your graveyard. -/
def hasAllCreatureTypes (g : Game) (o : GameObject) : Bool :=
  match o.controller with
  | none => false
  | some p =>
    o.staticAbilities.any fun
      | .getsAndAllTypesIfGyCreatureCards min _ _ => g.gyCreatureCards p >= min
      | _ => false

/-- Types an attached Aura adds, including the word "legendary". -/
def auraAddedTypes (g : Game) (o : GameObject) : Array String :=
  if !o.isOnBattlefield then #[]
  else
    g.battlefield.foldl (fun acc a =>
      if a.attachedTo != some o.id then acc
      else
        a.staticAbilities.foldl (fun acc ab =>
          match ab with
          | .enchantedCreatureGetsHasAndTypes _ _ _ types => acc ++ types
          | _ => acc) acc) #[]

/-- Whether `o` currently has subtype `s`, including Fog-style overwrites.
Changeling grants every creature type (CR 702.72 / MSH 72–73) unless a
type-setting Aura overwrites the subtypes. -/
def hasSubtype (g : Game) (o : GameObject) (s : String) : Bool :=
  let fogged :=
    g.battlefield.any (fun a =>
      a.attachedTo == some o.id &&
        a.staticAbilities.any (fun ab => ab.enchantedOnlySubtype?.isSome))
  (g.currentSubtypes o).any (· == s) ||
    (g.auraAddedTypes o).any (· == s) ||
    (!fogged && (o.printedOrUntilEot.changeling || g.hasAllCreatureTypes o) &&
      !isNoncreatureSubtype s)

/-- Printed legendary, or an Aura that adds the legendary supertype. -/
def treatedAsLegendary (g : Game) (o : GameObject) : Bool :=
  o.isLegendary ||
    (g.auraAddedTypes o).any (fun t => t == "legendary" || t == "Legendary")

/-- Continuous +P/+T `src` currently grants `target` as a lord (CR 604.2 / 613.3c). -/
def grantsStatBonusTo (g : Game) (src target : GameObject) : Int × Int :=
  src.staticAbilities.foldl
    (fun acc ab =>
      let sameController :=
        src.isOnBattlefield && target.isOnBattlefield &&
          src.controller == target.controller && src.controller.isSome &&
          target.isCreature
      match ab with
      | .otherSubtypeGetPowerPerArtifactToken subtype =>
        if sameController && src.id != target.id && g.hasSubtype target subtype then
          let n : Int :=
            match src.controller with
            | none => 0
            | some p =>
              Int.ofNat ((g.permanentsOf p).filter (fun o =>
                o.printed.isToken && o.printed.isArtifact) |>.size)
          addStats acc (n, 0)
        else acc
      | .opponentsCreaturesGet p t =>
        if src.isOnBattlefield && target.isOnBattlefield && target.isCreature &&
            src.controller.isSome && target.controller.isSome &&
            src.controller != target.controller then
          addStats acc (p, t)
        else acc
      | .chosenTypeCreaturesGet p t =>
        match src.status.chosenCreatureType with
        | some ty =>
          if sameController && g.hasSubtype target ty then addStats acc (p, t) else acc
        | none => acc
      | .creatureTokensGetOneAndVigilance =>
        if sameController && target.printed.isToken then addStats acc (1, 0) else acc
      | _ =>
        match ab.teamIfEnduringStory? with
        | some (pw, tw) =>
          if sameController && (src.controller.any g.hasEnduringStory) then
            addStats acc (pw, tw)
          else acc
        | none =>
          match ab.lordPump? with
          | none => acc
          | some (subtypes, p, t) =>
            let otherOk := src.id != target.id || ab.lordIncludesSelf
            let legendaryOk :=
              (!ab.lordLegendaryOnly || target.isLegendary) &&
              (!ab.lordNonlegendaryOnly || !target.isLegendary)
            let subtypeOk :=
              match src.status.chosenCreatureType with
              | some t => g.hasSubtype target t
              | none => subtypes.isEmpty || subtypes.any (g.hasSubtype target)
            if sameController && otherOk && legendaryOk && subtypeOk then
              addStats acc (p, t)
            else acc)
    (0, 0)

/-- Continuous +P/+T granted to `o` by permanents on the battlefield and
emblems in the command zone (CR 604.2 / 613.4c). -/
def lordStatBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield then (0, 0)
  else
    let fromPermanents :=
      g.battlefield.foldl
        (fun acc src => addStats acc (g.grantsStatBonusTo src o))
        (0, 0)
    match o.controller with
    | none => fromPermanents
    | some p =>
      if !o.isCreature then fromPermanents
      else
        let emblems :=
          (g.objects.filter (fun e => e.zone == .command && e.controlledBy p)).foldl
            (fun acc src =>
              let acc :=
                if src.printed.grantTeamPlusTwoFlying then addStats acc (2, 2) else acc
              src.staticAbilities.foldl (fun acc ab =>
                match ab with
                | .creaturesYouControlGet pw tw => addStats acc (pw, tw)
                | _ => acc) acc)
            (0, 0)
        addStats fromPermanents emblems

/-- Continuous +P/+T this Aura or Equipment currently grants its host (CR 613.3c). -/
def auraStatBonus (aura : GameObject) : Int × Int :=
  aura.staticAbilities.foldl
    (fun acc ab => addStats acc ab.hostStatBonus)
    (0, 0)

/-- Instant and sorcery cards in `p`'s graveyard (Glamdring). -/
def instantSorceryInGraveyard (g : Game) (p : PlayerId) : Nat :=
  (g.player p).graveyard.filter (fun id =>
    match g.findObject? id with
    | some c => c.printed.isInstant || c.printed.isSorcery
    | none => false) |>.size

/-- Static power/toughness from Auras and Equipment attached to `o` (CR 613.4c). -/
def attachedStatBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield then (0, 0)
  else
    g.battlefield.foldl
      (fun acc aura =>
        if aura.attachedTo == some o.id then
          let glam : Int × Int :=
            if aura.staticAbilities.any (fun
              | .equippedFirstStrikePlusPerInstantSorcery => true
              | _ => false) then
              match aura.controller with
              | some p => (Int.ofNat (g.instantSorceryInGraveyard p), 0)
              | none => (0, 0)
            else (0, 0)
          addStats acc
            (addStats (addStats (auraStatBonus aura) glam) ((aura.status.hone : Int), 0))
        else acc)
      (0, 0)

/-- Keywords granted while the controller has an enduring story. -/
def enduringStoryKeywords (g : Game) (o : GameObject) : Keywords :=
  if !o.isOnBattlefield then Keywords.none
  else
    match o.controller with
    | none => Keywords.none
    | some p =>
      if !g.hasEnduringStory p then Keywords.none
      else
        o.staticAbilities.foldl
          (fun acc ab =>
            match ab.selfIfEnduringStory? with
            | some (_, _, k) => Keywords.merge acc k
            | none => acc)
          Keywords.none

/-- Self +P/+T from `o`'s own Layer-7c static abilities and multi-turn pumps
(CR 613.4c). -/
def selfStatBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield then (0, 0)
  else
    let untilTurn :=
      o.status.untilTurnOfPump.foldl (fun acc (_, p, t) => addStats acc (p, t)) (0, 0)
    let mountain : Int × Int :=
      if o.printed.powerPerMountain == 0 then (0, 0)
      else
        let n :=
          (g.permanentsOf o.you).filter (fun p => g.hasSubtype p "Mountain") |>.size
        (Int.ofNat (o.printed.powerPerMountain * n), 0)
    let artifactPump : Int × Int :=
      if !o.status.pumpPerArtifactUntilEot then (0, 0)
      else
        let n : Int :=
          Int.ofNat ((g.permanentsOf o.you).filter (fun p =>
            p.printed.isArtifact || p.status.additionalArtifactUntilEot) |>.size)
        (n, n)
    let unspent : Int × Int :=
      match o.controller with
      | some p =>
        if o.printed.powerPerUnspentMana then
          let n : Int := Int.ofNat (g.player p).manaPool.total
          (n, n)
        else (0, 0)
      | none => (0, 0)
    let gyIds := (g.player o.you).graveyard
    let gy := gyIds.size
    let enduring := o.controller.any g.hasEnduringStory
    let fromAbilities :=
      o.staticAbilities.foldl (fun acc ab =>
        match ab.selfIfEnduringStory? with
        | some (pw, tw, _) => if enduring then addStats acc (pw, tw) else acc
        | none =>
          match ab.thresholdGets? with
          | some (pw, tw) =>
            if o.controller.isSome && gy >= 7 then addStats acc (pw, tw) else acc
          | none =>
            match ab with
            | .powerPerFatGraveyard p =>
              let n := g.players.filter (fun pl => pl.graveyard.size >= 7) |>.size
              addStats acc (p * (n : Int), 0)
            | .pt (.getsPowerPerControlled p attachedEquipment) =>
              let n : Int :=
                if attachedEquipment then Int.ofNat (g.attachedEquipmentCount o)
                else
                  Int.ofNat ((g.permanentsOf o.you).filter (fun x =>
                    x.id != o.id && x.printed.isArtifact) |>.size)
              addStats acc (p * n, 0)
            | .getsIfGyCreatureCards min pw tw
            | .getsAndAllTypesIfGyCreatureCards min pw tw =>
              let gyCreatures :=
                gyIds.filter (fun id => (g.object! id).printed.isCreature) |>.size
              if gyCreatures >= min then addStats acc (pw, tw) else acc
            | .powerPerSevenInGraveyard =>
              if o.controller.isSome then addStats acc (2 * Int.ofNat (gy / 7), 0) else acc
            | .powerPerCreatureAndPlaneswalkerCard =>
              if o.controller.isNone then acc
              else
                let n := (gyIds.filter (fun id =>
                  (g.findObject? id).any (fun c =>
                    c.printed.isCreature || c.printed.isPlaneswalker))).size
                addStats acc (Int.ofNat n, 0)
            | _ => acc) (0, 0)
    #[untilTurn, mountain, artifactPump, unspent, fromAbilities].foldl addStats (0, 0)

def snapshotPT (g : Game) (o : GameObject) : Int × Int :=
  let n : Int := (o.status.plusOnePlusOne : Int) - (o.status.minusOneMinusOne : Int)
  #[g.characteristicBasePT o, o.status.pump, (n, n), g.attachedStatBonus o,
      g.lordStatBonus o, g.selfStatBonus o].foldl
    addStats (0, 0)

/-- Power of `o` as last known information (CR 113.7a / 208.2). -/
def snapshotPower (g : Game) (o : GameObject) : Int :=
  (g.snapshotPT o).1

/-- Toughness of `o` as last known information (CR 113.7a / 208.2). -/
def snapshotToughness (g : Game) (o : GameObject) : Int :=
  (g.snapshotPT o).2

/-- Characteristic power before pumps, counters, and attached bonuses. -/
def basePower (g : Game) (o : GameObject) : Int :=
  g.characteristicBasePower o

/-- Characteristic toughness before pumps, counters, and attached bonuses. -/
def baseToughness (g : Game) (o : GameObject) : Int :=
  g.characteristicBaseToughness o

/-- Current power, including until-end-of-turn pumps, counters, land-count and
until-EOT base setting effects, attached bonuses, and lord bonuses (CR 208.2). -/
def power (g : Game) (o : GameObject) : Int :=
  g.snapshotPower o

/-- Current toughness, including until-end-of-turn pumps, counters, land-count and
until-EOT base setting effects, attached bonuses, and lord bonuses (CR 208.2). -/
def toughness (g : Game) (o : GameObject) : Int :=
  g.snapshotToughness o

/-- Greatest power among creatures `p` controls; `0` if they control none. -/
def greatestPowerAmongCreatures (g : Game) (p : PlayerId) : Int :=
  let creatures := g.creaturesControlledBy p
  if creatures.isEmpty then 0
  else creatures.foldl (fun acc o => max acc (g.power o)) (g.power creatures[0]!)

/-- Greatest power among attacking creatures `p` controls; `0` if none. -/
def greatestPowerAmongAttacking (g : Game) (p : PlayerId) : Int :=
  let attackers :=
    (g.permanentsOf p).filter (fun o => o.isCreature && o.status.attacking)
  if attackers.isEmpty then 0
  else attackers.foldl (fun acc o => max acc (g.power o)) (g.power attackers[0]!)

/-- Creatures currently blocking `attackerId`. -/
def blockersOf (g : Game) (attackerId : ObjectId) : Array GameObject :=
  g.battlefield.filter (fun b => b.status.blocking.contains attackerId)

/-- Attacking creatures `blocker` is still blocking (CR 510.1d). -/
def creaturesBlockedBy (g : Game) (blocker : GameObject) : Array GameObject :=
  blocker.status.blocking.filterMap (fun id =>
    match g.findObject? id with
    | some a =>
      if a.isOnBattlefield && a.status.attacking then some a else none
    | none => none)

end Game
end Mtg.Engine
