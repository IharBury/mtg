import Mtg.Engine.Game.Attachments

/-!
# Continuous stat bonuses (CR 613)

Layer-7c power/toughness additions: lords, Auras and Equipment,
enduring-story bonuses, graveyard- and artifact-count pumps, and the
P/T snapshots used for last-known values (CR 113.7a).
-/

namespace Mtg.Engine
namespace Game

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

/-- Whether `o` currently has subtype `s`, including Fog-style overwrites.
Changeling grants every creature type (CR 702.72 / MSH 72–73) unless a
type-setting Aura overwrites the subtypes. -/
def hasSubtype (g : Game) (o : GameObject) (s : String) : Bool :=
  let fogged :=
    g.battlefield.any (fun a =>
      a.attachedTo == some o.id &&
        a.staticAbilities.any (fun ab => ab.enchantedOnlySubtype?.isSome))
  (g.currentSubtypes o).any (· == s) ||
    (!fogged && o.printedOrUntilEot.changeling && !isNoncreatureSubtype s)

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
      | _ =>
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

/-- Continuous +P/+T granted to `o` by other permanents you control (CR 613.3c). -/
def lordStatBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield then (0, 0)
  else
    g.battlefield.foldl
      (fun acc src => addStats acc (g.grantsStatBonusTo src o))
      (0, 0)

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

/-- Static power/toughness from Auras and Equipment attached to `o`. -/
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

/-- Self +P/+T from “as long as you have an enduring story”. -/
def enduringStorySelfBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield then (0, 0)
  else
    match o.controller with
    | none => (0, 0)
    | some p =>
      if !g.hasEnduringStory p then (0, 0)
      else
        o.staticAbilities.foldl
          (fun acc ab =>
            match ab.selfIfEnduringStory? with
            | some (pw, tw, _) => addStats acc (pw, tw)
            | none => acc)
          (0, 0)

/-- Team +P/+T from “as long as you have an enduring story, creatures you
control get …”. -/
def enduringStoryTeamBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield || !o.isCreature then (0, 0)
  else
    match o.controller with
    | none => (0, 0)
    | some p =>
      if !g.hasEnduringStory p then (0, 0)
      else
        (g.permanentsOf p).foldl
          (fun acc src =>
            src.staticAbilities.foldl
              (fun acc ab =>
                match ab.teamIfEnduringStory? with
                | some (pw, tw) => addStats acc (pw, tw)
                | none => acc)
              acc)
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

/-- +P/+0 from `powerPerMountain` (e.g. Desert Were-Worm). -/
def mountainPowerBonus (g : Game) (o : GameObject) : Int :=
  if o.printed.powerPerMountain == 0 then 0
  else
    let n :=
      (g.permanentsOf o.you).filter (fun p => g.hasSubtype p "Mountain") |>.size
    Int.ofNat (o.printed.powerPerMountain * n)

/-- +P/+0 from graveyards with seven or more cards (Master's Councillors). -/
def fatGraveyardPowerBonus (g : Game) (o : GameObject) : Int :=
  o.staticAbilities.foldl (fun acc ab =>
    match ab with
    | .powerPerFatGraveyard p =>
      let n := g.players.filter (fun pl => pl.graveyard.size >= 7) |>.size
      acc + p * (n : Int)
    | _ => acc) 0

/-- Self +P/+T from leftover-lifted statics (other artifacts, attached
Equipment, creature cards in graveyard). -/
def leftoverSelfBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield then (0, 0)
  else
    o.staticAbilities.foldl (fun acc ab =>
      match ab with
      | .getsPowerPerOtherArtifact p =>
        let n : Int :=
          Int.ofNat ((g.permanentsOf o.you).filter (fun x =>
            x.id != o.id && x.printed.isArtifact) |>.size)
        addStats acc (p * n, 0)
      | .getsPowerPerAttachedEquipment p =>
        let n : Int := Int.ofNat (g.attachedEquipmentCount o)
        addStats acc (p * n, 0)
      | .getsIfGyCreatureCards min pw tw
      | .getsAndAllTypesIfGyCreatureCards min pw tw =>
        let gy :=
          (g.player o.you).graveyard.filter (fun id =>
            (g.object! id).printed.isCreature) |>.size
        if gy >= min then addStats acc (pw, tw) else acc
      | _ => acc) (0, 0)

/-- +1/+1 for each artifact you control (Iron Man Armor until EOT). -/
def artifactCountPump (g : Game) (o : GameObject) : Int × Int :=
  if !o.status.pumpPerArtifactUntilEot || !o.isOnBattlefield then (0, 0)
  else
    let n : Int :=
      Int.ofNat ((g.permanentsOf o.you).filter (fun p => p.printed.isArtifact ||
        p.status.additionalArtifactUntilEot) |>.size)
    (n, n)

def snapshotPT (g : Game) (o : GameObject) : Int × Int :=
  let n : Int := o.status.plusOnePlusOne
  #[g.characteristicBasePT o, o.status.pump, (n, n), g.attachedStatBonus o,
      g.lordStatBonus o, g.enduringStorySelfBonus o, g.enduringStoryTeamBonus o,
      (g.mountainPowerBonus o, (0 : Int)),
      (g.fatGraveyardPowerBonus o, (0 : Int)),
      g.artifactCountPump o, g.leftoverSelfBonus o].foldl
    addStats (0, 0)

/-- Power of `o` as last known information (CR 113.7a / 208.2). -/
def snapshotPower (g : Game) (o : GameObject) : Int :=
  (g.snapshotPT o).1

/-- Toughness of `o` as last known information (CR 113.7a / 208.2). -/
def snapshotToughness (g : Game) (o : GameObject) : Int :=
  (g.snapshotPT o).2

end Game
end Mtg.Engine
