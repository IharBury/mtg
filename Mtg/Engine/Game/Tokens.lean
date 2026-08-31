import Mtg.Engine.Game.Allocation

/-!
# Tokens (CR 111)

Printed definitions of the tokens the engine creates, and token creation
including create-multipliers and Food/Treasure replacement effects.
-/

namespace Mtg.Engine
namespace Game

/-- A Treasure token (CR 111 / 701.42). -/
def treasureToken : CardDef := {
  name := "Treasure"
  types := #[.artifact]
  subtypes := #["Treasure"]
  oracleText := "{T}, Sacrifice this artifact: Add one mana of any color."
  tapSacrificeAddAnyColor := true
  isToken := true
}

/-- A creature token. `color` is the color indicator (CR 202.2e). -/
def creatureToken (name : String) (subtypes : Array String)
    (power toughness : Int) (color : Option Color := none)
    (keywords : Keywords := Keywords.none)
    (types : Array CardType := #[.creature]) : CardDef := {
  name
  types
  subtypes
  power := some power
  toughness := some toughness
  colorIndicator := color.map ColorSet.singleton
  keywords
  isToken := true
}

/-- A 1/1 white Human Soldier creature token. -/
def humanSoldierToken : CardDef :=
  creatureToken "Human Soldier" #["Human", "Soldier"] 1 1 (some .white)

/-- Additional +1/+1 counters from Arwen, Weaver of Hope as `entering` enters.
Only weavers already on the battlefield before timestamp `asOf` apply
(simultaneous enters do not see each other). -/
def hopeCountersOnEnter (g : Game) (entering : GameObject) (asOf : Nat) : Nat :=
  match entering.controller with
  | none => 0
  | some p =>
    if !entering.isCreature then 0
    else
      (g.permanentsOf p).foldl (fun acc weaver =>
        if weaver.id == entering.id then acc
        else if !weaver.printed.othersEnterWithPlusOneEqualToughness then acc
        else if weaver.timestamp >= asOf then acc
        else acc + weaver.toughness.toNat) 0

/-- Put `n` additional +1/+1 counters on `o` as it enters from hope-weaver
replacements. -/
def applyHopeEnterCounters (g : Game) (o : GameObject) (asOf : Nat) : Game :=
  let n := g.hopeCountersOnEnter o asOf
  if n == 0 then g
  else
    let o := { o with status := o.status.addPlusOnePlusOne n }
    (g.setObject o).logMsg s!"{o.name} enters with {n} additional +1/+1 counter(s)"

/-- Create one token without replacement effects (CR 111.2 / 608.2c). Callers
that must let enters-the-battlefield triggers see the token (amass, recruit)
invoke `afterPermanentEnters` after this returns. -/
def createOneToken (g : Game) (controller : PlayerId) (printed : CardDef)
    (tapped := false) : Game × GameObject :=
  if (g.player controller).lost then
    (g.logMsg "no token is created (CR 800.4b)",
      { id := ⟨0⟩, printed := { printed with isToken := true },
        owner := controller, zone := .command })
  else
    let printed := { printed with isToken := true }
    let sick := printed.isCreature && !printed.keywords.haste
    let asOf := g.timestamp
    let (g, obj) := g.allocObject printed controller .battlefield (some controller)
      (status := { tapped := tapped, summoningSick := sick })
    let g := g.logMsg s!"{(g.player controller).name} creates {obj.name}"
    let g := g.applyHopeEnterCounters (g.object! obj.id) asOf
    -- Storied is not a trigger; an artifact token can be the third permanent.
    let g := g.refreshEnduringStory
    (g, g.object! obj.id)

/-- How many times a token-creating event is replaced (`2^n` for `n`
token-doublers such as Bard, King of Dale). -/
def tokenCreateMultiplier (g : Game) (controller : PlayerId) : Nat :=
  let n := (g.permanentsOf controller).filter (fun o => o.printed.tokenDoubling) |>.size
  Nat.pow 2 n

/-- Extra Treasures created alongside each Food (Bilbo, Fellow Conspirator). -/
def foodTreasureReplacements (g : Game) (controller : PlayerId) : Nat :=
  (g.permanentsOf controller).filter (fun o => o.printed.foodAlsoCreatesTreasure) |>.size

/-- Create a token under `controller`, applying token-doubling and
Food-and-Treasure replacement effects. -/
def createToken (g : Game) (controller : PlayerId) (printed : CardDef)
    (tapped := false) : Game × GameObject :=
  if (g.player controller).lost then
    g.createOneToken controller printed (tapped := tapped)
  else
    let copies := g.tokenCreateMultiplier controller
    let extraTreasure :=
      if printed.hasSubtype "Food" then g.foodTreasureReplacements controller else 0
    Id.run do
      let mut g := g
      let mut last : Option GameObject := none
      for _ in [0:copies] do
        let (g', obj) := g.createOneToken controller printed (tapped := tapped)
        g := g'
        last := some obj
      for _ in [0:copies * extraTreasure] do
        let (g', _) := g.createOneToken controller treasureToken (tapped := tapped)
        g := g'
      match last with
      | some obj => (g, g.object! obj.id)
      | none => (g, g.object! ⟨0⟩)

/-- Create `n` Treasure tokens, optionally tapped. -/
def createTreasureTokens (g : Game) (controller : PlayerId) (n : Nat)
    (tapped := false) : Game :=
  if (g.player controller).lost then
    if n == 0 then g else g.logMsg "no token is created (CR 800.4b)"
  else
  Id.run do
    let mut g := g
    for _ in [0:n] do
      let (g', _) := g.createToken controller treasureToken (tapped := tapped)
      g := g'
    return g

/-- A 0/0 black Army creature token of the given subtype (amass). -/
def armyToken (subtype : String) : CardDef := {
  name := s!"{subtype} Army"
  types := #[.creature]
  subtypes := #[subtype, "Army"]
  power := some 0
  toughness := some 0
  colorIndicator := some (ColorSet.singleton .black)
  isToken := true
}

/-- A 0/0 black Goblin Army creature token (amass Goblins). -/
def goblinArmyToken : CardDef := armyToken "Goblin"

/-- A 0/0 black Orc Army creature token (amass Orcs). -/
def orcArmyToken : CardDef := armyToken "Orc"

/-- A 0/0 black Zombie Army creature token (amass Zombies). -/
def zombieArmyToken : CardDef := armyToken "Zombie"

/-- A Food token (CR 111 / 701.34). -/
def foodToken : CardDef := {
  name := "Food"
  types := #[.artifact]
  subtypes := #["Food"]
  oracleText := "{2}, {T}, Sacrifice this artifact: You gain 3 life."
  activatedAbilities := #[{
    cost := { mana := ManaCost.ofGeneric 2, tap := true, sacrificeSource := true }
    effect := Effect.gainLife 3
  }]
  isToken := true
}

def wolfToken : CardDef :=
  creatureToken "Wolf" #["Wolf"] 2 2 (some .green)

def dwarfToken : CardDef :=
  creatureToken "Dwarf" #["Dwarf"] 2 2 (some .red)

def bearToken : CardDef :=
  creatureToken "Bear" #["Bear"] 2 2 (some .green)

def elfToken : CardDef :=
  creatureToken "Elf" #["Elf"] 1 1 (some .green)

/-- A 1/1 white Spirit creature token with flying. -/
def spiritToken : CardDef :=
  creatureToken "Spirit" #["Spirit"] 1 1 (some .white) Keyword.flying

/-- A 4/4 white Bird Soldier creature token with flying. -/
def birdSoldierToken : CardDef :=
  creatureToken "Bird Soldier" #["Bird", "Soldier"] 4 4 (some .white) Keyword.flying

/-- A 6/6 red Dragon creature token with flying. -/
def dragonToken : CardDef :=
  creatureToken "Dragon" #["Dragon"] 6 6 (some .red) Keyword.flying

/-- A 3/1 colorless Wall artifact creature token with defender. -/
def wallToken : CardDef :=
  creatureToken "Stone Boulder" #["Wall"] 3 1 none Keyword.defender
    (types := #[.artifact, .creature])

/-- A colorless Equipment artifact token named Axe. -/
def axeToken : CardDef := {
  name := "Axe"
  types := #[.artifact]
  subtypes := #["Equipment"]
  staticAbilities := #[.equippedCreatureGets 1 0]
  activatedAbilities := #[
    { cost := { mana := ManaCost.ofGeneric 2 }
      effect := Effect.attachToTargetCreatureYouControl
      onlyAsSorcery := true }
  ]
  isToken := true
}

/-- A Clue artifact token (CR 701.55). -/
def clueToken : CardDef := {
  name := "Clue"
  types := #[.artifact]
  subtypes := #["Clue"]
  oracleText := "{2}, Sacrifice this token: Draw a card."
  activatedAbilities := #[{
    cost := { mana := ManaCost.ofGeneric 2, sacrificeSource := true }
    effect := Effect.abilityDraw 1
  }]
  isToken := true
}

/-- A 3/2 white Hero creature token with vigilance. -/
def hero32vigilanceToken : CardDef :=
  creatureToken "Hero" #["Hero"] 3 2 (some .white) Keyword.vigilance

/-- A 2/1 black Villain creature token with menace. -/
def villain21menaceToken : CardDef :=
  creatureToken "Villain" #["Villain"] 2 1 (some .black) Keyword.menace

/-- A 2/2 colorless Robot Villain artifact creature token. -/
def robotVillain22Token : CardDef :=
  creatureToken "Robot Villain" #["Robot", "Villain"] 2 2 none
    (types := #[.artifact, .creature])

/-- A 6/5 blue Leviathan creature token with hexproof. -/
def leviathan65hexproofToken : CardDef :=
  creatureToken "Leviathan" #["Leviathan"] 6 5 (some .blue) Keyword.hexproof

/-- A 1/1 white Soldier creature token. -/
def soldier11whiteToken : CardDef :=
  creatureToken "Soldier" #["Soldier"] 1 1 (some .white)

/-- A 1/1 green Squirrel creature token. -/
def squirrel11greenToken : CardDef :=
  creatureToken "Squirrel" #["Squirrel"] 1 1 (some .green)

/-- A 0/4 colorless Wall creature token with defender. -/
def wall04defenderToken : CardDef :=
  creatureToken "Wall" #["Wall"] 0 4 none Keyword.defender

/-- A 3/3 colorless Robot Villain artifact creature token named Doombot. -/
def doombotToken : CardDef :=
  creatureToken "Doombot" #["Robot", "Villain"] 3 3 none
    (types := #[.artifact, .creature])

/-- A 1/1 green Insect creature token. -/
def insect11greenToken : CardDef :=
  creatureToken "Insect" #["Insect"] 1 1 (some .green)

/-- A 1/1 green Minion creature token named Moloid. -/
def moloidToken : CardDef :=
  creatureToken "Moloid" #["Minion"] 1 1 (some .green)

/-- A 1/1 red Alien creature token with haste that attacks each combat if able. -/
def alien11redHasteToken : CardDef := {
  name := "Alien"
  types := #[.creature]
  subtypes := #["Alien"]
  power := some 1
  toughness := some 1
  colorIndicator := some (ColorSet.singleton .red)
  keywords := Keyword.haste
  oracleText := "Haste\nThis token attacks each combat if able."
  staticAbilities := #[.attacksEachCombatIfAble]
  isToken := true
}

/-- A predefined Vibranium artifact token (MSH). Indestructible; `{T}: Add {C}`
that cannot be spent to cast a nonartifact spell. -/
def vibraniumToken : CardDef := {
  name := "Vibranium"
  types := #[.artifact]
  subtypes := #["Vibranium"]
  oracleText := "Indestructible\n{T}: Add {C}. This mana can't be spent to cast a nonartifact spell."
  keywords := Keyword.indestructible
  tapAddMana := #[.colorless]
  isToken := true
}

/-- Printed characteristics for a `TokenKind`. -/
def tokenPrinted (k : TokenKind) : CardDef :=
  match k with
  | .treasure => treasureToken
  | .food => foodToken
  | .humanSoldier => humanSoldierToken
  | .wolf => wolfToken
  | .dwarf => dwarfToken
  | .bear => bearToken
  | .elf => elfToken
  | .spirit => spiritToken
  | .birdSoldier => birdSoldierToken
  | .wall => wallToken
  | .dragon => dragonToken
  | .clue => clueToken
  | .hero32vigilance => hero32vigilanceToken
  | .villain21menace => villain21menaceToken
  | .robotVillain22 => robotVillain22Token
  | .leviathan65hexproof => leviathan65hexproofToken
  | .soldier11white => soldier11whiteToken
  | .squirrel11green => squirrel11greenToken
  | .wall04defender => wall04defenderToken
  | .doombot => doombotToken
  | .insect11green => insect11greenToken
  | .vibranium => vibraniumToken
  | .moloid => moloidToken

/-- Create `n` tokens of `kind`. -/
def createKindTokens (g : Game) (controller : PlayerId) (kind : TokenKind)
    (n : Nat) (tapped := false) (attacking := false) : Game :=
  if (g.player controller).lost then
    if n == 0 then g else g.logMsg "no token is created (CR 800.4b)"
  else
  Id.run do
    let mut g := g
    let dest := if attacking then some g.defendingPlayer else none
    for _ in [0:n] do
      let (g', obj) := g.createToken controller (tokenPrinted kind) (tapped := tapped)
      g := g'
      if attacking then
        g := g.setObject { (g.object! obj.id) with
          status := { (g.object! obj.id).status with
            attacking := true
            attackingWhom := dest } }
    return g

end Game
end Mtg.Engine
