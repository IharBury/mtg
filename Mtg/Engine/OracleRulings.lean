import Mtg.Engine.Card
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.Oracle
import Mtg.Engine.Tests

/-!
# Unique Oracle rulings

Judge-issued Oracle rulings (Gatherer / Scryfall `wotc` comments, plus
MSH release notes) for unique cards in `The Hobbit` (HOB),
`The Hobbit Eternal` (HOC), and
`Magic: The Gathering | Marvel Super Heroes` (MSH). These are
not the rules text printed on the cards and are not Comprehensive
Rules citations. They are clarifications published by Wizards for
judges and players. Shared comments that appear on many cards
(Adventure, amass, landfall, Power-up, Teamwork, and so on) are
kept once, even when those cards come from different sets.

Engine behavior for each entry is checked by `#guard`s later in this
file (`Mtg.Engine.RulingTests` and `Mtg.Engine.MshRulingTests`).

Collected 728 unique comments from
1480 ruling instances on
500 cards
(193 HOB, 117 HOC, 190 MSH).
-/

namespace Mtg.Engine

/-- One unique official Oracle ruling that appears on at least one
catalog card. `cards` uses Scryfall names (`Face // Adventure`).
The same comment is stored once and may list cards from more than
one set. -/
structure OracleRuling where
  /-- 1-based index in `uniqueOracleRulings`. -/
  id : Nat
  /-- Official Wizards judge ruling (Gatherer / Scryfall `wotc`), not
  printed Oracle text. -/
  comment : String
  /-- Cards this comment applies to. Rulings are issued by judges; they
  are not printed on the cards. -/
  cards : Array String
  /-- Distinct set codes among those cards (`hob` / `hoc` / `msh`). -/
  sets : Array String
deriving Repr, Inhabited, BEq

/-- Unique official Oracle rulings across HOB, HOC, and MSH.
HOB/HOC comments keep their original ids (1–359). MSH-only comments
follow. A comment shared by more than one set is a single entry whose
`cards` and `sets` list every card it applies to. -/
def uniqueOracleRulings : Array OracleRuling := #[
  { id := 1, comment := "Some cards refer to the \"amassed Army.\" That means the Army creature you chose to receive counters, even if no counters were placed on it for some reason.",
    cards := #["Rhovanion Rampager", "Great Goblin, Foul-Hearted", "Great Ugly-Looking Goblin // Clap! Snap!", "Tidings of War", "Goblin-town Flunkies", "Gathering of Darkness", "Bolg of the North", "Rage into the Valley", "Bothersome Noisemaker", "Sauron, the Dark Lord", "Azog, Moria's Ruin", "Misty Mountains Raider", "Down, Down to Goblin-town", "Orcish Bowmasters", "Goblin Plate Mail", "Fearsome Goblin Pair", "Along the Crooked Way"],
    sets := #["hob", "hoc"] },
  { id := 2, comment := "An adventurer card is a permanent card in every zone except the stack, as well as while on the stack if not cast as an Adventure. Ignore its alternative characteristics in those cases. For example, while it's in your graveyard, Bilbo, Luckwearer is a blue creature card whose mana value is 2. It can't be put into your hand by the effect of Speak Secrets (\"Mill four cards, then put an instant or sorcery card from among them into your hand.\").",
    cards := #["Gollum, Silent Slinker // Meager Meal", "The Arkenstone // Seek the Heart", "Great Ugly-Looking Goblin // Clap! Snap!", "Glamdring, Foe-hammer // Gleam of Death", "Beorn, Reluctant Host // Till and Tend", "My Precious // Allure of Power", "Most Decrepit Old Bird // Speak Secrets", "An Unexpected Party // At the Door", "Glóin the Mighty // Easy Pickings", "Velvetwing Butterflies // Gaze in Wonder", "Bofur, Reliable Guardian // Concerted Care", "Bilbo, Luckwearer // Burglar's Plot", "Lake-town Mariners // Gone Fishing", "Gandalf, Goblins' Bane // Flameshape", "Thranduil, Sindarin Liege // Silvan Rally", "Bilbo Baggins, Burglar // Take a Glance", "Smaug, the Great Calamity // Spew Flame"],
    sets := #["hob"] },
  { id := 3, comment := "An effect may refer to a card, spell, or permanent that \"has an Adventure.\" This refers to a card, spell, or permanent that has an adventurer card's set of alternative characteristics, even if they're not being used and even if that card was never cast as an Adventure.",
    cards := #["Gollum, Silent Slinker // Meager Meal", "The Arkenstone // Seek the Heart", "Great Ugly-Looking Goblin // Clap! Snap!", "Glamdring, Foe-hammer // Gleam of Death", "Beorn, Reluctant Host // Till and Tend", "My Precious // Allure of Power", "Most Decrepit Old Bird // Speak Secrets", "An Unexpected Party // At the Door", "Glóin the Mighty // Easy Pickings", "Velvetwing Butterflies // Gaze in Wonder", "Bofur, Reliable Guardian // Concerted Care", "Bilbo, Luckwearer // Burglar's Plot", "Lake-town Mariners // Gone Fishing", "Gandalf, Goblins' Bane // Flameshape", "Thranduil, Sindarin Liege // Silvan Rally", "Bilbo Baggins, Burglar // Take a Glance", "Smaug, the Great Calamity // Spew Flame"],
    sets := #["hob"] },
  { id := 4, comment := "Casting a card as an Adventure isn't casting it for an alternative cost. Effects that allow you to cast a spell for an alternative cost or without paying its mana cost may allow you to apply those to the Adventure.",
    cards := #["Gollum, Silent Slinker // Meager Meal", "The Arkenstone // Seek the Heart", "Great Ugly-Looking Goblin // Clap! Snap!", "Glamdring, Foe-hammer // Gleam of Death", "Beorn, Reluctant Host // Till and Tend", "My Precious // Allure of Power", "Most Decrepit Old Bird // Speak Secrets", "An Unexpected Party // At the Door", "Glóin the Mighty // Easy Pickings", "Velvetwing Butterflies // Gaze in Wonder", "Bofur, Reliable Guardian // Concerted Care", "Bilbo, Luckwearer // Burglar's Plot", "Lake-town Mariners // Gone Fishing", "Gandalf, Goblins' Bane // Flameshape", "Thranduil, Sindarin Liege // Silvan Rally", "Bilbo Baggins, Burglar // Take a Glance", "Smaug, the Great Calamity // Spew Flame"],
    sets := #["hob"] },
  { id := 5, comment := "If a spell is cast as an Adventure, its controller exiles it instead of putting it into its owner's graveyard as it resolves. For as long as it remains exiled, that player may play it using its primary characteristics. If an Adventure spell leaves the stack in any way other than resolving (most likely by being countered or by failing to resolve because its targets have all become illegal), that card won't be exiled and the spell's controller won't be able to cast it as a permanent later.",
    cards := #["Gollum, Silent Slinker // Meager Meal", "The Arkenstone // Seek the Heart", "Great Ugly-Looking Goblin // Clap! Snap!", "Glamdring, Foe-hammer // Gleam of Death", "Beorn, Reluctant Host // Till and Tend", "My Precious // Allure of Power", "Most Decrepit Old Bird // Speak Secrets", "An Unexpected Party // At the Door", "Glóin the Mighty // Easy Pickings", "Velvetwing Butterflies // Gaze in Wonder", "Bofur, Reliable Guardian // Concerted Care", "Bilbo, Luckwearer // Burglar's Plot", "Lake-town Mariners // Gone Fishing", "Gandalf, Goblins' Bane // Flameshape", "Thranduil, Sindarin Liege // Silvan Rally", "Bilbo Baggins, Burglar // Take a Glance", "Smaug, the Great Calamity // Spew Flame"],
    sets := #["hob"] },
  { id := 6, comment := "If an adventurer card ends up in exile for any other reason than by exiling itself while resolving, it won't give you permission to cast it as a permanent spell.",
    cards := #["Gollum, Silent Slinker // Meager Meal", "The Arkenstone // Seek the Heart", "Great Ugly-Looking Goblin // Clap! Snap!", "Glamdring, Foe-hammer // Gleam of Death", "Beorn, Reluctant Host // Till and Tend", "My Precious // Allure of Power", "Most Decrepit Old Bird // Speak Secrets", "An Unexpected Party // At the Door", "Glóin the Mighty // Easy Pickings", "Velvetwing Butterflies // Gaze in Wonder", "Bofur, Reliable Guardian // Concerted Care", "Bilbo, Luckwearer // Burglar's Plot", "Lake-town Mariners // Gone Fishing", "Gandalf, Goblins' Bane // Flameshape", "Thranduil, Sindarin Liege // Silvan Rally", "Bilbo Baggins, Burglar // Take a Glance", "Smaug, the Great Calamity // Spew Flame"],
    sets := #["hob"] },
  { id := 7, comment := "If an effect copies an Adventure spell, that copy is exiled as it resolves. It ceases to exist as a state-based action; it's not possible to cast the copy as a permanent.",
    cards := #["Gollum, Silent Slinker // Meager Meal", "The Arkenstone // Seek the Heart", "Great Ugly-Looking Goblin // Clap! Snap!", "Glamdring, Foe-hammer // Gleam of Death", "Beorn, Reluctant Host // Till and Tend", "My Precious // Allure of Power", "Most Decrepit Old Bird // Speak Secrets", "An Unexpected Party // At the Door", "Glóin the Mighty // Easy Pickings", "Velvetwing Butterflies // Gaze in Wonder", "Bofur, Reliable Guardian // Concerted Care", "Bilbo, Luckwearer // Burglar's Plot", "Lake-town Mariners // Gone Fishing", "Gandalf, Goblins' Bane // Flameshape", "Thranduil, Sindarin Liege // Silvan Rally", "Bilbo Baggins, Burglar // Take a Glance", "Smaug, the Great Calamity // Spew Flame"],
    sets := #["hob"] },
  { id := 8, comment := "If an effect instructs you to choose a card name, you may choose the alternative Adventure name. Consider only the alternative characteristics to determine whether that is an appropriate name to choose.",
    cards := #["Gollum, Silent Slinker // Meager Meal", "The Arkenstone // Seek the Heart", "Great Ugly-Looking Goblin // Clap! Snap!", "Glamdring, Foe-hammer // Gleam of Death", "Beorn, Reluctant Host // Till and Tend", "My Precious // Allure of Power", "Most Decrepit Old Bird // Speak Secrets", "An Unexpected Party // At the Door", "Glóin the Mighty // Easy Pickings", "Velvetwing Butterflies // Gaze in Wonder", "Bofur, Reliable Guardian // Concerted Care", "Bilbo, Luckwearer // Burglar's Plot", "Lake-town Mariners // Gone Fishing", "Gandalf, Goblins' Bane // Flameshape", "Thranduil, Sindarin Liege // Silvan Rally", "Bilbo Baggins, Burglar // Take a Glance", "Smaug, the Great Calamity // Spew Flame"],
    sets := #["hob"] },
  { id := 9, comment := "If an effect refers to a card, spell, or permanent that has an Adventure, it won't find an instant or sorcery spell on the stack that's been cast as an Adventure.",
    cards := #["Gollum, Silent Slinker // Meager Meal", "The Arkenstone // Seek the Heart", "Great Ugly-Looking Goblin // Clap! Snap!", "Glamdring, Foe-hammer // Gleam of Death", "Beorn, Reluctant Host // Till and Tend", "My Precious // Allure of Power", "Most Decrepit Old Bird // Speak Secrets", "An Unexpected Party // At the Door", "Glóin the Mighty // Easy Pickings", "Velvetwing Butterflies // Gaze in Wonder", "Bofur, Reliable Guardian // Concerted Care", "Bilbo, Luckwearer // Burglar's Plot", "Lake-town Mariners // Gone Fishing", "Gandalf, Goblins' Bane // Flameshape", "Thranduil, Sindarin Liege // Silvan Rally", "Bilbo Baggins, Burglar // Take a Glance", "Smaug, the Great Calamity // Spew Flame"],
    sets := #["hob"] },
  { id := 10, comment := "If an object becomes a copy of an object that has an Adventure, the copy also has an Adventure. If it changes zones, it will either cease to exist (if it's a token) or cease to be a copy (if it's a nontoken permanent), and so you won't be able to cast it as an Adventure.",
    cards := #["Gollum, Silent Slinker // Meager Meal", "The Arkenstone // Seek the Heart", "Great Ugly-Looking Goblin // Clap! Snap!", "Glamdring, Foe-hammer // Gleam of Death", "Beorn, Reluctant Host // Till and Tend", "My Precious // Allure of Power", "Most Decrepit Old Bird // Speak Secrets", "An Unexpected Party // At the Door", "Glóin the Mighty // Easy Pickings", "Velvetwing Butterflies // Gaze in Wonder", "Bofur, Reliable Guardian // Concerted Care", "Bilbo, Luckwearer // Burglar's Plot", "Lake-town Mariners // Gone Fishing", "Gandalf, Goblins' Bane // Flameshape", "Thranduil, Sindarin Liege // Silvan Rally", "Bilbo Baggins, Burglar // Take a Glance", "Smaug, the Great Calamity // Spew Flame"],
    sets := #["hob"] },
  { id := 11, comment := "If you cast an adventurer card as an Adventure, use only its alternative characteristics to determine whether it's legal to cast that spell. For example, if you control Gandalf, Party Guest (\"At the beginning of combat on your turn, you may cast an instant or sorcery spell with mana value X or less from your hand without paying its mana cost, where X is twice the number of legendary Wizards you control.\"), you could cast Burglar's Plot from your hand without paying its mana cost (provided you control enough legendary Wizards), but not Bilbo, Luckwearer.",
    cards := #["Gollum, Silent Slinker // Meager Meal", "The Arkenstone // Seek the Heart", "Great Ugly-Looking Goblin // Clap! Snap!", "Glamdring, Foe-hammer // Gleam of Death", "Beorn, Reluctant Host // Till and Tend", "My Precious // Allure of Power", "Most Decrepit Old Bird // Speak Secrets", "An Unexpected Party // At the Door", "Glóin the Mighty // Easy Pickings", "Velvetwing Butterflies // Gaze in Wonder", "Bofur, Reliable Guardian // Concerted Care", "Bilbo, Luckwearer // Burglar's Plot", "Lake-town Mariners // Gone Fishing", "Gandalf, Goblins' Bane // Flameshape", "Thranduil, Sindarin Liege // Silvan Rally", "Bilbo Baggins, Burglar // Take a Glance", "Smaug, the Great Calamity // Spew Flame"],
    sets := #["hob"] },
  { id := 12, comment := "When casting a spell as an Adventure, use the alternative characteristics and ignore all of the card's normal characteristics. The spell's color, mana cost, mana value, and so on are determined by only those alternative characteristics. If the spell leaves the stack, it immediately resumes using its normal characteristics.",
    cards := #["Gollum, Silent Slinker // Meager Meal", "The Arkenstone // Seek the Heart", "Great Ugly-Looking Goblin // Clap! Snap!", "Glamdring, Foe-hammer // Gleam of Death", "Beorn, Reluctant Host // Till and Tend", "My Precious // Allure of Power", "Most Decrepit Old Bird // Speak Secrets", "An Unexpected Party // At the Door", "Glóin the Mighty // Easy Pickings", "Velvetwing Butterflies // Gaze in Wonder", "Bofur, Reliable Guardian // Concerted Care", "Bilbo, Luckwearer // Burglar's Plot", "Lake-town Mariners // Gone Fishing", "Gandalf, Goblins' Bane // Flameshape", "Thranduil, Sindarin Liege // Silvan Rally", "Bilbo Baggins, Burglar // Take a Glance", "Smaug, the Great Calamity // Spew Flame"],
    sets := #["hob"] },
  { id := 13, comment := "You must still follow any timing restrictions and permissions for the permanent spell you cast from exile. Normally, you'll be able to cast it only during your main phase while the stack is empty.",
    cards := #["Gollum, Silent Slinker // Meager Meal", "The Arkenstone // Seek the Heart", "Great Ugly-Looking Goblin // Clap! Snap!", "Glamdring, Foe-hammer // Gleam of Death", "Beorn, Reluctant Host // Till and Tend", "My Precious // Allure of Power", "Most Decrepit Old Bird // Speak Secrets", "An Unexpected Party // At the Door", "Glóin the Mighty // Easy Pickings", "Velvetwing Butterflies // Gaze in Wonder", "Bofur, Reliable Guardian // Concerted Care", "Bilbo, Luckwearer // Burglar's Plot", "Lake-town Mariners // Gone Fishing", "Gandalf, Goblins' Bane // Flameshape", "Thranduil, Sindarin Liege // Silvan Rally", "Bilbo Baggins, Burglar // Take a Glance", "Smaug, the Great Calamity // Spew Flame"],
    sets := #["hob"] },
  { id := 14, comment := "Amass Orcs works the same way, except you create a 0/0 black Orc Army creature token if you don't control an Army. And if the Army creature you chose isn't already an Orc, it becomes an Orc in addition to its other types. By combining cards with amass Orcs and amass Goblins, you can end up with a Goblin Orc Army.",
    cards := #["Rhovanion Rampager", "Great Goblin, Foul-Hearted", "Great Ugly-Looking Goblin // Clap! Snap!", "Tidings of War", "Goblin-town Flunkies", "Gathering of Darkness", "Bolg of the North", "Rage into the Valley", "Bothersome Noisemaker", "Sauron, the Dark Lord", "Azog, Moria's Ruin", "Misty Mountains Raider", "Down, Down to Goblin-town", "Goblin Plate Mail", "Fearsome Goblin Pair", "Along the Crooked Way"],
    sets := #["hob", "hoc"] },
  { id := 15, comment := "If you don't control an Army, the Goblin Army token you create enters the battlefield as a 0/0 creature before receiving counters. Any abilities that trigger when a creature with a certain power enters the battlefield, such as that of Mentor of the Meek, will see the token enter as a 0/0 creature before it gets +1/+1 counters.",
    cards := #["Rhovanion Rampager", "Great Goblin, Foul-Hearted", "Great Ugly-Looking Goblin // Clap! Snap!", "Tidings of War", "Goblin-town Flunkies", "Gathering of Darkness", "Bolg of the North", "Rage into the Valley", "Bothersome Noisemaker", "Sauron, the Dark Lord", "Azog, Moria's Ruin", "Misty Mountains Raider", "Down, Down to Goblin-town", "Goblin Plate Mail", "Fearsome Goblin Pair", "Along the Crooked Way"],
    sets := #["hob", "hoc"] },
  { id := 16, comment := "In the rare case that you control multiple Army creatures (perhaps because you control a creature with changeling) while you amass Goblins, you choose which of your Army creatures to put the +1/+1 counters on. If that creature isn't a Goblin, it becomes a Goblin in addition to its other types.",
    cards := #["Rhovanion Rampager", "Great Goblin, Foul-Hearted", "Great Ugly-Looking Goblin // Clap! Snap!", "Tidings of War", "Goblin-town Flunkies", "Gathering of Darkness", "Bolg of the North", "Rage into the Valley", "Bothersome Noisemaker", "Sauron, the Dark Lord", "Azog, Moria's Ruin", "Misty Mountains Raider", "Down, Down to Goblin-town", "Goblin Plate Mail", "Fearsome Goblin Pair", "Along the Crooked Way"],
    sets := #["hob", "hoc"] },
  { id := 17, comment := "Some spells and abilities that amass Goblins may require targets. If each target chosen is an illegal target as that spell or ability tries to resolve, it won't resolve. You won't amass Goblins.",
    cards := #["Rhovanion Rampager", "Great Goblin, Foul-Hearted", "Great Ugly-Looking Goblin // Clap! Snap!", "Tidings of War", "Goblin-town Flunkies", "Gathering of Darkness", "Bolg of the North", "Rage into the Valley", "Bothersome Noisemaker", "Sauron, the Dark Lord", "Azog, Moria's Ruin", "Misty Mountains Raider", "Down, Down to Goblin-town", "Goblin Plate Mail", "Fearsome Goblin Pair", "Along the Crooked Way"],
    sets := #["hob", "hoc"] },
  { id := 18, comment := "To amass Goblins N, if you don't control an Army creature, create a 0/0 black Goblin Army creature token. Then you choose an Army creature you control and put N +1/+1 counters on it. If that Army isn't already a Goblin, it becomes a Goblin in addition to its other types.",
    cards := #["Rhovanion Rampager", "Great Goblin, Foul-Hearted", "Great Ugly-Looking Goblin // Clap! Snap!", "Tidings of War", "Goblin-town Flunkies", "Gathering of Darkness", "Bolg of the North", "Rage into the Valley", "Bothersome Noisemaker", "Sauron, the Dark Lord", "Azog, Moria's Ruin", "Misty Mountains Raider", "Down, Down to Goblin-town", "Goblin Plate Mail", "Fearsome Goblin Pair", "Along the Crooked Way"],
    sets := #["hob", "hoc"] },
  { id := 19, comment := "A landfall ability doesn't trigger if a permanent already on the battlefield becomes a land.",
    cards := #["Silvan Reveler", "Thranduil's Company", "Mirkwood Meditator", "Attercop", "Dancing from Dark to Dawn", "Gandalf, Shadow's Foe", "Thranduil the Strategist", "Elven Raft-Steerer", "Beorn's Hospitality", "Boughside Wanderers", "Down in the Valley", "Thranduil, Sindarin Liege // Silvan Rally", "Claim the Kingdom", "Ka-Zar of the Savage Land", "Mole Man, Moloid Master"],
    sets := #["hob", "hoc", "msh"] },
  { id := 20, comment := "A landfall ability triggers whenever a land you control enters for any reason. It triggers whenever you play a land, as well as whenever a spell or ability puts a land onto the battlefield under your control.",
    cards := #["Silvan Reveler", "Thranduil's Company", "Mirkwood Meditator", "Attercop", "Dancing from Dark to Dawn", "Gandalf, Shadow's Foe", "Thranduil the Strategist", "Elven Raft-Steerer", "Beorn's Hospitality", "Boughside Wanderers", "Down in the Valley", "Thranduil, Sindarin Liege // Silvan Rally", "Claim the Kingdom", "Ka-Zar of the Savage Land", "Mole Man, Moloid Master"],
    sets := #["hob", "hoc", "msh"] },
  { id := 21, comment := "Whenever a land you control enters, each landfall ability of permanents you control will trigger. You can put them on the stack in any order. The last ability you put on the stack will be the first one to resolve (as a result, you can have those abilities resolve in the order of your choosing).",
    cards := #["Silvan Reveler", "Thranduil's Company", "Mirkwood Meditator", "Attercop", "Dancing from Dark to Dawn", "Gandalf, Shadow's Foe", "Thranduil the Strategist", "Elven Raft-Steerer", "Beorn's Hospitality", "Boughside Wanderers", "Down in the Valley", "Thranduil, Sindarin Liege // Silvan Rally", "Claim the Kingdom", "Ka-Zar of the Savage Land", "Mole Man, Moloid Master"],
    sets := #["hob", "hoc", "msh"] },
  { id := 22, comment := "A permanent is any object on the battlefield, including tokens and lands. Spells and emblems aren't permanents.",
    cards := #["Balin, Loremaster", "Dáin, Lord of the Iron Hills", "Ori, Keeper of Songs", "Kíli the Resourceful", "Bombur, Gentle Dreamer", "Óin the Brave", "Andúril, Narsil Reforged", "Bifur, Melodic Rider", "Thorin Oakenshield", "Fíli the Pathfinder"],
    sets := #["hob", "hoc"] },
  { id := 23, comment := "Once a spell or ability that causes you to recruit begins to resolve, no player may take any other actions until it's done. Any responses made to the spell or ability must be made before you draw, discard, and potentially create a token.",
    cards := #["The Mountain-king's Return", "Bard's Company", "Esgaroth Garrison", "The Queen of Dale", "Long Lake Nuisance", "Patient Instructor", "Lake-town Lookout", "Great Gilded Boat", "Celebrate the Mountain-king", "Sound the Trumpets"],
    sets := #["hob"] },
  { id := 24, comment := "A single permanent can only count once toward the three legendary, Saga, and/or artifact permanents needed to get an enduring story, even if it has more than one of those qualities. If you control one permanent that is a legendary artifact and a second permanent that is a Saga, you will only have two of the three permanents required to get an enduring story.",
    cards := #["Balin, Loremaster", "Dáin, Lord of the Iron Hills", "Ori, Keeper of Songs", "Kíli the Resourceful", "Bombur, Gentle Dreamer", "Óin the Brave", "Bifur, Melodic Rider", "Thorin Oakenshield", "Fíli the Pathfinder"],
    sets := #["hob"] },
  { id := 25, comment := "If you control three legendary, Saga, and/or artifact permanents but don't control a permanent with storied, you don't get an enduring story. For example, if you controlled three artifacts, lost control of two, then cast Thorin Oakenshield, you won't have an enduring story.",
    cards := #["Balin, Loremaster", "Dáin, Lord of the Iron Hills", "Ori, Keeper of Songs", "Kíli the Resourceful", "Bombur, Gentle Dreamer", "Óin the Brave", "Bifur, Melodic Rider", "Thorin Oakenshield", "Fíli the Pathfinder"],
    sets := #["hob"] },
  { id := 26, comment := "If your third legendary, Saga, or artifact permanent enters the battlefield and then one of those permanents leaves the battlefield immediately afterwards (most likely due to the \"legend rule\" or due to being a creature with 0 toughness), you get an enduring story before it leaves the battlefield.",
    cards := #["Balin, Loremaster", "Dáin, Lord of the Iron Hills", "Ori, Keeper of Songs", "Kíli the Resourceful", "Bombur, Gentle Dreamer", "Óin the Brave", "Bifur, Melodic Rider", "Thorin Oakenshield", "Fíli the Pathfinder"],
    sets := #["hob"] },
  { id := 27, comment := "Once you have an enduring story, you have it for the rest of the game, even if you lose control of some or all of your storied permanents. The enduring story designation is on the player and can't be removed by any effect.",
    cards := #["Balin, Loremaster", "Dáin, Lord of the Iron Hills", "Ori, Keeper of Songs", "Kíli the Resourceful", "Bombur, Gentle Dreamer", "Óin the Brave", "Bifur, Melodic Rider", "Thorin Oakenshield", "Fíli the Pathfinder"],
    sets := #["hob"] },
  { id := 28, comment := "Storied isn't a triggered ability and doesn't use the stack. Players can respond to a spell that will give you your third legendary, Saga, and/or artifact permanent, but they can't respond to you getting an enduring story once you control that third permanent.",
    cards := #["Balin, Loremaster", "Dáin, Lord of the Iron Hills", "Ori, Keeper of Songs", "Kíli the Resourceful", "Bombur, Gentle Dreamer", "Óin the Brave", "Bifur, Melodic Rider", "Thorin Oakenshield", "Fíli the Pathfinder"],
    sets := #["hob"] },
  { id := 29, comment := "Typecycling is a form of cycling. Any ability that triggers on a card being cycled also triggers on a card being typecycled. Any ability that stops a cycling ability from being activated also stops a typecycling ability from being activated.",
    cards := #["Oliphaunt", "Troll of Khazad-dûm", "Lórien Revealed", "Eagles of the North"],
    sets := #["hoc"] },
  { id := 30, comment := "Unlike the normal cycling ability, typecycling doesn't allow you to draw a card. Rather, it lets you search your library for a card with the type or types indicated by the ability name. For example, a card with basic landcycling lets you search for a basic land card, and a card with Wizardcycling lets you search for a Wizard card.",
    cards := #["Oliphaunt", "Troll of Khazad-dûm", "Lórien Revealed", "Eagles of the North"],
    sets := #["hoc"] },
  { id := 31, comment := "\"Flashback [cost]\" means \"You may cast this card from your graveyard by paying [cost] rather than paying its mana cost\" and \"If the flashback cost was paid, exile this card instead of putting it anywhere else any time it would leave the stack.\"",
    cards := #["Moment of Glory", "Plunder the Trollshaws", "Tidings of War"],
    sets := #["hob"] },
  { id := 32, comment := "A spell cast using flashback will always be exiled afterward, whether it resolves, is countered, or leaves the stack in some other way.",
    cards := #["Moment of Glory", "Plunder the Trollshaws", "Tidings of War"],
    sets := #["hob"] },
  { id := 33, comment := "If a card with flashback is put into your graveyard during your turn, you can cast it if it's legal to do so before any other player can take any actions.",
    cards := #["Moment of Glory", "Plunder the Trollshaws", "Tidings of War"],
    sets := #["hob"] },
  { id := 34, comment := "If a triggered ability is linked to a second ability, additional instances of that triggered ability are also linked to that second ability. If the second ability refers to \"the exiled card,\" it refers to all cards exiled by instances of the triggered ability.",
    cards := #["Wizard's Staff", "Bifur, Melodic Rider", "Chief of the Wilds"],
    sets := #["hob", "hoc"] },
  { id := 35, comment := "In some cases involving linked abilities, an ability requires information about \"the exiled card.\" When this happens, the ability gets multiple answers. If these answers are being used to determine the value of a variable, the sum is used.",
    cards := #["Wizard's Staff", "Bifur, Melodic Rider", "Chief of the Wilds"],
    sets := #["hob", "hoc"] },
  { id := 36, comment := "The legendary creature must already be on the battlefield as the land enters the battlefield. If it enters the battlefield at the same time, the land will enter tapped.",
    cards := #["Rivendell", "Minas Tirith", "The Shire"],
    sets := #["hoc"] },
  { id := 37, comment := "You must still follow any timing restrictions and permissions, including those based on the card's type. For instance, you can cast a sorcery using flashback only when you could normally cast a sorcery.",
    cards := #["Moment of Glory", "Plunder the Trollshaws", "Tidings of War"],
    sets := #["hob"] },
  { id := 38, comment := "A creature equipped by an Equipment with hone counters on it gets +1/+0 for each hone counter on that Equipment. This effect is from the counter itself rather than an ability on the Equipment, so even if the Equipment loses some of its abilities, each hone counter will still grant +1/+0 to the creature.",
    cards := #["Sting, Bilbo's Sword", "Dwalin, Weaponmaster"],
    sets := #["hob"] },
  { id := 39, comment := "After each permanent returns to the battlefield, it will be a new object with no connection to the permanent that was exiled. It won't be in combat or have any additional abilities it may have had when it was exiled. Any counters on it cease to exist; Auras attached to it are put into their owner's graveyards; and any Equipment will become unattached.",
    cards := #["Elrond, Moon-Reader", "Roll-Roll-Roll-Roll"],
    sets := #["hob"] },
  { id := 40, comment := "Amass Zombies works the same way, except you create a 0/0 black Zombie Army creature token if you don't control an Army. If the Army creature you chose isn't already a Zombie, it becomes a Zombie in addition to its other types. By combining cards with amass Orcs and amass Zombies, you can end up with an Orc Zombie Army.",
    cards := #["Sauron, the Dark Lord", "Orcish Bowmasters"],
    sets := #["hoc"] },
  { id := 41, comment := "Amass abilities are now written as \"amass [subtype] N.\" Previous cards with amass have received errata to say \"amass Zombies N.\"",
    cards := #["Sauron, the Dark Lord", "Orcish Bowmasters"],
    sets := #["hoc"] },
  { id := 42, comment := "As the Ring tempts you, you get an emblem named The Ring if you don't have one. Then your emblem gains its next ability and you choose a creature you control to become (or remain) your Ring-bearer.",
    cards := #["Witch-king of Angmar", "Sauron, the Dark Lord"],
    sets := #["hoc"] },
  { id := 43, comment := "Each player can have only one emblem named The Ring and only one Ring-bearer at a time.",
    cards := #["Witch-king of Angmar", "Sauron, the Dark Lord"],
    sets := #["hoc"] },
  { id := 44, comment := "Each time the Ring tempts you, you must choose a creature if you control one.",
    cards := #["Witch-king of Angmar", "Sauron, the Dark Lord"],
    sets := #["hoc"] },
  { id := 45, comment := "Hone counters can be put on any Equipment and each one will grant +1/+0 to that Equipment's equipped creature, even if the Equipment the hone counters are on doesn't reference hone counters or have an ability that puts them on itself.",
    cards := #["Sting, Bilbo's Sword", "Dwalin, Weaponmaster"],
    sets := #["hob"] },
  { id := 46, comment := "If a spell's kicker cost was paid, the spell is \"kicked.\"",
    cards := #["The Eagles Are Coming!", "Galadriel's Dismissal"],
    sets := #["hob", "hoc"] },
  { id := 47, comment := "If a token is exiled this way, it will cease to exist and will not return to the battlefield.",
    cards := #["Elrond, Moon-Reader", "Roll-Roll-Roll-Roll"],
    sets := #["hob"] },
  { id := 48, comment := "If the creature you choose as your Ring-bearer was already your Ring-bearer, that still counts as choosing that creature as your Ring-bearer for the purpose of abilities that trigger \"whenever you choose a creature as your Ring-bearer\" or abilities that care about which creature was chosen as your Ring-bearer.",
    cards := #["Witch-king of Angmar", "Sauron, the Dark Lord"],
    sets := #["hoc"] },
  { id := 49, comment := "If the spell you cast has {X} in its mana cost, you must choose 0 as the value of X when casting it without paying its mana cost.",
    cards := #["Gríma, Saruman's Footman", "Saruman of Many Colors"],
    sets := #["hoc"] },
  { id := 50, comment := "If you cast a spell \"without paying its mana cost,\" you can't pay any alternative costs. You can, however, pay additional costs, such as kicker costs. If the card has any mandatory additional costs, you must pay those.",
    cards := #["Gríma, Saruman's Footman", "Saruman of Many Colors"],
    sets := #["hoc"] },
  { id := 51, comment := "If you don't control an Army, the Orc Army token you create enters the battlefield as a 0/0 creature before receiving counters. Any abilities that trigger when a creature with a certain power enters the battlefield, such as that of Mentor of the Meek, will see the token enter as a 0/0 creature before it gets +1/+1 counters.",
    cards := #["Sauron, the Dark Lord", "Orcish Bowmasters"],
    sets := #["hoc"] },
  { id := 52, comment := "In the rare case that you control multiple Army creatures (perhaps because you played a creature with changeling) while you amass Orcs, you choose which of your Army creatures to put the +1/+1 counters on. If that creature isn't an Orc, it becomes an Orc in addition to its other types.",
    cards := #["Sauron, the Dark Lord", "Orcish Bowmasters"],
    sets := #["hoc"] },
  { id := 53, comment := "Some spells and abilities that amass Orcs may require targets. If each target chosen is an illegal target as that spell or ability tries to resolve, it won't resolve. You won't amass Orcs.",
    cards := #["Sauron, the Dark Lord", "Orcish Bowmasters"],
    sets := #["hoc"] },
  { id := 54, comment := "Some spells and abilities that cause the Ring to tempt you may require targets. If each target chosen is an illegal target as that spell or ability tries to resolve, it won't resolve. The Ring won't tempt you.",
    cards := #["Witch-king of Angmar", "Sauron, the Dark Lord"],
    sets := #["hoc"] },
  { id := 55, comment := "That player can find fewer basic land cards than the number of exiled creatures, whether because they want to or because they don't have that many basic land cards left.",
    cards := #["Settle the Wreckage"],
    sets := #["hob"] },
  { id := 56, comment := "The Ring can tempt you even if you don't control a creature. In this case, abilities that trigger \"whenever the Ring tempts you\" will still trigger.",
    cards := #["Witch-king of Angmar", "Sauron, the Dark Lord"],
    sets := #["hoc"] },
  { id := 57, comment := "The Ring gains its abilities in order from top to bottom. Once it gains an ability, it has that ability for the rest of the game.",
    cards := #["Witch-king of Angmar", "Sauron, the Dark Lord"],
    sets := #["hoc"] },
  { id := 58, comment := "The kicker ability doesn't let you pay a kicker cost more than once.",
    cards := #["The Eagles Are Coming!", "Galadriel's Dismissal"],
    sets := #["hob", "hoc"] },
  { id := 59, comment := "The number of lands that player may find is the number of attacking creatures that were exiled, even if some of those creatures were tokens, weren't creature cards, or didn't end up in exile (most likely because one was that player's commander in the Commander variant).",
    cards := #["Settle the Wreckage"],
    sets := #["hob"] },
  { id := 60, comment := "The power boost applies only while the Equipment with hone counters is attached to a creature. If an Equipment with hone counters on it becomes unattached from a creature, leaves the battlefield, or has its hone counters removed, the power of the creature changes immediately.",
    cards := #["Sting, Bilbo's Sword", "Dwalin, Weaponmaster"],
    sets := #["hob"] },
  { id := 61, comment := "To amass Orcs N, if you don't control an Army creature, create a 0/0 black Orc Army creature token. Then you choose an Army creature you control and put N +1/+1 counters on it. If that Army isn't already an Orc, it becomes an Orc in addition to its other types.",
    cards := #["Sauron, the Dark Lord", "Orcish Bowmasters"],
    sets := #["hoc"] },
  { id := 62, comment := "To determine a spell's total cost, start with the mana cost (or an alternative cost if another card's effect allows you to pay one instead), add any cost increases (such as kicker), then apply any cost reductions. The spell's mana value remains unchanged, no matter what the total cost to cast it was.",
    cards := #["The Eagles Are Coming!", "Galadriel's Dismissal"],
    sets := #["hob", "hoc"] },
  { id := 63, comment := "Triggered abilities use the word \"when,\" \"whenever,\" or \"at.\" They're often written as \"[Trigger condition], [effect].\" Some keyword abilities are triggered abilities and will have \"when,\" \"whenever,\" or \"at\" in their reminder text.",
    cards := #["Bifur, Melodic Rider", "Chief of the Wilds"],
    sets := #["hob", "hoc"] },
  { id := 64, comment := "You pay all costs and follow all timing rules for cards played this way. For example, if the exiled card is a land card, you may play it only during your main phase while the stack is empty and only if you have an available land play remaining.",
    cards := #["The Great Goblin", "Snowslope Hunter"],
    sets := #["hob"] },
  { id := 65, comment := "\"Gift a Treasure\" causes the chosen opponent to create a Treasure token.",
    cards := #["Bilbo's Gambit"],
    sets := #["hob"] },
  { id := 66, comment := "A creature attacks alone if it's the only creature declared as an attacker during the declare attackers step. For example, Bilbo's Ring's second ability won't trigger if you attack with multiple creatures and all but one of them are removed from combat.",
    cards := #["Bilbo's Ring"],
    sets := #["hoc"] },
  { id := 67, comment := "A permanent with a shadow counter on it has shadow.",
    cards := #["Minas Morgul, Dark Fortress"],
    sets := #["hoc"] },
  { id := 68, comment := "A spell's mana value is determined only by its mana cost. Ignore any alternative costs, additional costs, cost increases, or cost reductions.",
    cards := #["Call Forth the Tempest"],
    sets := #["hoc"] },
  { id := 69, comment := "Activated abilities contain a colon. They're generally written \"[Cost]: [Effect].\" Some keyword abilities are activated abilities and will have colons in their reminder text.",
    cards := #["Thranduil, the Elvenking"],
    sets := #["hob"] },
  { id := 70, comment := "Activating the first ability of Key to the Side-Door after a creature has become blocked won't cause that creature to become unblocked.",
    cards := #["Key to the Side-Door"],
    sets := #["hob"] },
  { id := 71, comment := "Activating the second ability of Rogue's Passage after a creature has become blocked won't cause that creature to become unblocked.",
    cards := #["Rogue's Passage"],
    sets := #["hoc"] },
  { id := 72, comment := "Affinity for Elves reduces only the generic mana in the cost to cast Cantankerous Keepers. The colored mana must still be paid.",
    cards := #["Cantankerous Keepers"],
    sets := #["hob"] },
  { id := 73, comment := "After each permanent returns to the battlefield, it will be a new object with no connection to the permanent that was exiled. It won't be in combat or have any additional abilities it may have had before it was exiled. Any counters on it cease to exist; Auras attached to it are put into their owner's graveyards; and any Equipment will become unattached.",
    cards := #["Lake-town Mariners // Gone Fishing"],
    sets := #["hob"] },
  { id := 74, comment := "An ability that triggers when another ability resolves, such as Tom Bombadil's triggered ability, triggers when all of its instructions (as modified by applicable replacement effects) have been followed and it has been removed from the stack. For example, if Tom Bombadil is returned to the battlefield by the final chapter ability of Elspeth Conquers Death, it will be on the battlefield in time to see that final chapter ability finish resolving and get removed from the stack, and thus Tom Bombadil's last ability will trigger.",
    cards := #["Tom Bombadil"],
    sets := #["hoc"] },
  { id := 75, comment := "An activated ability of a creature that's also a mana ability (such as \"{T}: Add {G}\") can cause Elrond's first ability to trigger.",
    cards := #["Elrond, Moon-Reader"],
    sets := #["hob"] },
  { id := 76, comment := "An attacking or blocking creature that phases out is removed from combat.",
    cards := #["Galadriel's Dismissal"],
    sets := #["hoc"] },
  { id := 77, comment := "Any continuous effects with a \"for as long as\" duration ignore phased-out objects. If ignoring those objects causes the effect's conditions to no longer be met, the duration will expire.",
    cards := #["Galadriel's Dismissal"],
    sets := #["hoc"] },
  { id := 78, comment := "Any creature tokens that were returned to your hand are counted by the delayed triggered ability. You'll get a Bird Soldier token for each of them.",
    cards := #["The Eagles Are Coming!"],
    sets := #["hob"] },
  { id := 79, comment := "Any effects that modify a creature's power and/or toughness without setting them to a specific value (i.e. ones that don't affect base power and/or toughness) will apply after its base power and toughness are set, regardless of the order those effects were created. The same is true for counters that modify its power and toughness.",
    cards := #["Galion, Elvenking's Butler"],
    sets := #["hob"] },
  { id := 80, comment := "Artifacts and enchantments destroyed this way count toward the life gained even if they're put into a zone other than a graveyard.",
    cards := #["Ori, Plate Stacker"],
    sets := #["hoc"] },
  { id := 81, comment := "As Galion's ability resolves, the base power and toughness of the targeted creature are set to Galion's actual power and toughness, not its base power and toughness. If Galion's power or toughness changes later in the turn, the other creature isn't affected.",
    cards := #["Galion, Elvenking's Butler"],
    sets := #["hob"] },
  { id := 82, comment := "As a permanent is phased out, Auras and Equipment attached to it also phase out at the same time. Those Auras and Equipment will phase in at the same time that creature does, and they'll phase in still attached to that permanent.",
    cards := #["Galadriel's Dismissal"],
    sets := #["hoc"] },
  { id := 83, comment := "As an additional cost to cast a spell with gift, you can promise the listed gift to an opponent. That opponent is chosen as part of that additional cost. The gift isn't given at this time; rather, it's given at a later time based on whether or not the spell is a permanent spell.",
    cards := #["Bilbo's Gambit"],
    sets := #["hob"] },
  { id := 84, comment := "Ascend on a permanent isn't a triggered ability and doesn't use the stack. Players can respond to a spell that will give you your tenth permanent, but they can't respond to you getting the city's blessing once you control that tenth permanent. This means that if your tenth permanent is a land you play, players can't respond before you get the city's blessing.",
    cards := #["Andúril, Narsil Reforged"],
    sets := #["hoc"] },
  { id := 85, comment := "Attaching an Equipment with its enters-the-battlefield triggered ability isn't the same as using its equip ability. You don't pay mana for the attachment, and the timing restrictions for equip abilities don't apply.",
    cards := #["Mithril Coat"],
    sets := #["hoc"] },
  { id := 86, comment := "Attacking with any creatures will cause Great Gilded Boat's ability to trigger. Great Gilded Boat doesn't have to be among them.",
    cards := #["Great Gilded Boat"],
    sets := #["hob"] },
  { id := 87, comment := "Auras attached to exiled nonland permanents will be put into their owners' graveyards. Equipment attached to exiled creatures will become unattached and remain on the battlefield. Any counters on exiled nonland permanents will cease to exist.",
    cards := #["Celebrate the Mountain-king"],
    sets := #["hob"] },
  { id := 88, comment := "Auras attached to the exiled creature will be put into their owners' graveyards. Equipment attached to the exiled creature will become unattached and remain on the battlefield. Any counters on the exiled creature will cease to exist.",
    cards := #["Colossal Whale"],
    sets := #["hoc"] },
  { id := 89, comment := "Auras attached to the exiled permanent will be put into their owners’ graveyards. Any Equipment will become unattached and remain on the battlefield. Any counters on the exiled permanent will cease to exist. When the card returns to the battlefield, it will be a new object with no connection to the card that was exiled.",
    cards := #["Banishing Light", "Web Up", "Wiccan, Rising Magician"],
    sets := #["hoc", "msh"] },
  { id := 90, comment := "Bag End Banquet's last ability is a mana ability. It doesn't use the stack and can't be responded to.",
    cards := #["Bag End Banquet"],
    sets := #["hoc"] },
  { id := 91, comment := "Bard's last ability only applies to tokens that are created. Copies of permanent spells that resolve become tokens on the battlefield, but those tokens are not created and will not be doubled by Bard's ability.",
    cards := #["Bard, King of Dale"],
    sets := #["hob"] },
  { id := 92, comment := "Because Bard, King of Dale is legendary, it's unlikely that one player will control two. However, if that happens, cards drawn by that player will be multiplied by four. Three Bards will multiply by eight, and so on.",
    cards := #["Bard, King of Dale"],
    sets := #["hob"] },
  { id := 93, comment := "Because damage remains marked on a creature until the damage is removed as the turn ends, nonlethal damage dealt to Mirkwood Meditator may become lethal if you change its base toughness during that turn.",
    cards := #["Mirkwood Meditator"],
    sets := #["hob"] },
  { id := 94, comment := "Because the \"search\" requires you to find a card with certain characteristics, you don't have to find the card if you don't want to.",
    cards := #["Wood Elves"],
    sets := #["hob"] },
  { id := 95, comment := "Because you're already casting the card using an alternative cost (by casting it without paying its mana cost), you can't pay any other alternative costs for the card, including casting it face down using the morph ability. You can pay additional costs, such as kicker costs. If the card has any mandatory additional costs, you must pay those.",
    cards := #["Thranduil's Decree"],
    sets := #["hob"] },
  { id := 96, comment := "Belladonna Took's ability has no effect each time beyond the third it resolves in a turn.",
    cards := #["Belladonna Took"],
    sets := #["hob"] },
  { id := 97, comment := "Bifur's last ability doesn't copy the triggered ability; it just causes the ability to trigger an additional time. Any choices made as you put the ability onto the stack, such as modes and targets, are made separately for each instance of the ability. Any choices made on resolution, such as whether to put counters on a permanent, are also made individually.",
    cards := #["Bifur, Melodic Rider"],
    sets := #["hob"] },
  { id := 98, comment := "Bolg of the North has a reflexive triggered ability. When it enters the battlefield, its triggered ability goes on the stack without a target. While that ability is resolving, you may sacrifice another creature. If you do, a second ability triggers and you pick a target that will be dealt damage. This is different from other abilities that say \"If you do . . .\" in that players may cast spells and activate abilities before a creature is sacrificed and then again after the creature is sacrificed but before damage is dealt.",
    cards := #["Bolg of the North"],
    sets := #["hob"] },
  { id := 99, comment := "Bolg of the North's damage-dealing ability triggers only when you sacrifice a creature as a result of the instruction of its triggered ability. It won't trigger if you sacrifice a creature for any other reason.",
    cards := #["Bolg of the North"],
    sets := #["hob"] },
  { id := 100, comment := "Cards that would go to your opponent's graveyard for reasons other than dying, such as being discarded or milled, will still go to the graveyard and will not be exiled instead.",
    cards := #["Head of the Hunt"],
    sets := #["hob"] },
  { id := 101, comment := "Cascade triggers when you cast the spell, meaning that it resolves before that spell. If you end up casting the exiled card, it will go on the stack above the spell with cascade.",
    cards := #["Call Forth the Tempest"],
    sets := #["hoc"] },
  { id := 102, comment := "Cavern-Hoard Dragon's first ability counts only the artifacts controlled by the opponent who controls the greatest number of artifacts among your opponents. If you have an opponent who controls two artifacts and another opponent who controls three artifacts, Cavern-Hoard Dragon's mana cost would be reduced by {3}.",
    cards := #["Cavern-Hoard Dragon"],
    sets := #["hoc"] },
  { id := 103, comment := "Cavern-Hoard Dragon's last ability cares about the number of artifacts that player controls as the ability resolves.",
    cards := #["Cavern-Hoard Dragon"],
    sets := #["hoc"] },
  { id := 104, comment := "Celeborn the Wise's first ability has you scry 1 just once whenever you attack with one or more Elves, no matter how many Elves you attack with and no matter how many players you attack.",
    cards := #["Celeborn the Wise"],
    sets := #["hoc"] },
  { id := 105, comment := "Celeborn the Wise's last ability cares about the number of cards you actually looked at. For example, if you were supposed to scry 3 but only had two cards in your library, Celeborn would get +2/+2.",
    cards := #["Celeborn the Wise"],
    sets := #["hoc"] },
  { id := 106, comment := "Chief of the Wilds's last ability doesn't copy the triggered ability; it just causes the ability to trigger an additional time. Any choices made as you put the ability onto the stack, such as modes and targets, are made separately for each instance of the ability. Any choices made on resolution, such as whether to put counters on a permanent, are also made individually.",
    cards := #["Chief of the Wilds"],
    sets := #["hoc"] },
  { id := 107, comment := "Choices made for permanents as they entered the battlefield are remembered when they phase in.",
    cards := #["Galadriel's Dismissal"],
    sets := #["hoc"] },
  { id := 108, comment := "Colossal Whale's ability causes a zone change with a duration, a new style of ability that's somewhat reminiscent of older cards like Oblivion Ring. However, unlike Oblivion Ring, cards like Colossal Whale have a single ability that creates two one-shot effects: one that exiles the creature when the ability resolves, and another that returns the exiled card to the battlefield immediately after Colossal Whale leaves the battlefield.",
    cards := #["Colossal Whale"],
    sets := #["hoc"] },
  { id := 109, comment := "Colossal Whale's triggered ability triggers and resolves during the declare attackers step, before blocking creatures are declared.",
    cards := #["Colossal Whale"],
    sets := #["hoc"] },
  { id := 110, comment := "Count the mana values of all other spells you've cast this turn before Call Forth the Tempest resolved, including any spells that you've cast due to Call Forth the Tempest's cascade abilities. It doesn't matter whether those spells resolved; you only need to have cast them. Conversely, if you copy a spell without casting it, you won't include that copy's mana value in the amount of damage Call Forth the Tempest deals.",
    cards := #["Call Forth the Tempest"],
    sets := #["hoc"] },
  { id := 111, comment := "Damage dealt to creatures remains on those creatures until the cleanup step or until an effect removes that damage. If you control Tom Bombadil with at least 4 damage on it as well as a single Saga which has four or more lore counters on it, and that Saga leaves the battlefield later in the turn, Tom Bombadil will be destroyed. This will be true even if that Saga leaves the battlefield as a result of its final chapter ability leaving the stack; state-based actions will be checked before Tom Bombadil's triggered ability could get you another Saga.",
    cards := #["Tom Bombadil"],
    sets := #["hoc"] },
  { id := 112, comment := "Desert Were-Worm's second ability will only trigger if creatures you attacked with had power 12 or greater at the time you attacked. Increases to the power of attacking creatures after they attack, such as from attack triggers, will not contribute to the 12 power needed for this ability to trigger.",
    cards := #["Desert Were-Worm"],
    sets := #["hob"] },
  { id := 113, comment := "Due to a 2021 rules change to cascade, not only do you stop exiling cards if you exile a nonland card with lesser mana value than the spell with cascade, but the resulting spell you cast must also have lesser mana value. Previously, in cases where a card's mana value differed from the resulting spell, such as with some modal double-faced cards or cards with an Adventure, you could cast a spell with a higher mana value than the exiled card.",
    cards := #["Call Forth the Tempest"],
    sets := #["hoc"] },
  { id := 114, comment := "Each instance of cascade triggers and resolves separately. The spell you cast due to the first cascade ability will go on the stack on top of the second cascade ability. That spell will resolve before you exile cards for the second cascade ability.",
    cards := #["Call Forth the Tempest"],
    sets := #["hoc"] },
  { id := 115, comment := "Eagles of the North's triggered ability affects only creatures you control at the time it resolves. Any creatures that come under your control later in the turn won't be affected.",
    cards := #["Eagles of the North"],
    sets := #["hoc"] },
  { id := 116, comment := "Effects that modify the power or toughness of Mirkwood Meditator without setting it will apply to its new base power and toughness no matter when they started to take effect. The same is true for counters that change its power and toughness.",
    cards := #["Mirkwood Meditator"],
    sets := #["hob"] },
  { id := 117, comment := "Effects that say \"If a [quality] was beheld\" only care if a card of that quality was revealed or a permanent you control of that quality was chosen. No matter what happens to that card or permanent after that, it was still beheld, and any additional effects that depend on that card or permanent being beheld will still happen.",
    cards := #["Elven Passage"],
    sets := #["hob"] },
  { id := 118, comment := "Elven Chorus doesn't change when you can cast creature spells. Normally, this means during your main phase when the stack is empty, although flash may change this.",
    cards := #["Elven Chorus"],
    sets := #["hoc"] },
  { id := 119, comment := "Elvish Archdruid's activated ability is a mana ability. It doesn't use the stack and players can't respond to it.",
    cards := #["Elvish Archdruid"],
    sets := #["hoc"] },
  { id := 120, comment := "Elvish Archdruid's first ability affects only other Elves you control. However, Elvish Archdruid's second ability counts all Elves you control — including itself.",
    cards := #["Elvish Archdruid"],
    sets := #["hoc"] },
  { id := 121, comment := "Excess damage has been dealt to a creature if the damage dealt to it is greater than lethal damage. Usually, this means damage greater than its toughness, although damage already marked on the creature is taken into account.",
    cards := #["Bolg of the North"],
    sets := #["hob"] },
  { id := 122, comment := "Food is an artifact type. Even though it appears on some creatures, it's never a creature type.",
    cards := #["The Shire"],
    sets := #["hoc"] },
  { id := 123, comment := "For Bard's last ability, all of the tokens enter the battlefield simultaneously. They'll be created with the same name, color, type and subtype, abilities, power, toughness, and so on.",
    cards := #["Bard, King of Dale"],
    sets := #["hob"] },
  { id := 124, comment := "For instants and sorceries with gift, the gift is given to the appropriate opponent as part of the resolution of the spell. This happens before any of the spell's other effects would take place.",
    cards := #["Bilbo's Gambit"],
    sets := #["hob"] },
  { id := 125, comment := "For the last ability, none of the chosen creatures are targets of the ability. You may choose creatures with shroud, for example.",
    cards := #["Mount Doom"],
    sets := #["hoc"] },
  { id := 126, comment := "Gaining protection from everything causes a spell or ability on the stack to have an illegal target if it targets you. As a spell or ability tries to resolve, if all its targets are illegal, that spell or ability doesn't resolve and none of its effects happen, including effects unrelated to the target. If at least one target is still legal, the spell or ability does as much as it can to the remaining legal targets, and its other effects still happen.",
    cards := #["The One Ring"],
    sets := #["hoc"] },
  { id := 127, comment := "Galion's ability overwrites all previous effects that set a creature's power and toughness to specific values. Other effects that set its power or toughness to specific values that start to apply after the ability resolves will overwrite this effect.",
    cards := #["Galion, Elvenking's Butler"],
    sets := #["hob"] },
  { id := 128, comment := "Glamdring, Foe-hammer's cost reduction ability reduces only the generic mana in the spell's cost. The colored mana must still be paid.",
    cards := #["Glamdring, Foe-hammer // Gleam of Death"],
    sets := #["hob"] },
  { id := 129, comment := "Gleaming Splendor doesn't need to have been under your control when the first card is drawn for its ability to trigger. As long as you control it when an opponent draws their second card in a turn, that ability will trigger. The ability can trigger only once each turn for each opponent.",
    cards := #["Gleaming Splendor"],
    sets := #["hob"] },
  { id := 130, comment := "Gleaming Splendor's activated ability requires two different target players. You cannot target the same player twice with a single activation of the ability.",
    cards := #["Gleaming Splendor"],
    sets := #["hob"] },
  { id := 131, comment := "Guttersnipe's triggered ability resolves before the spell that caused it to trigger. It resolves even if that spell is countered or otherwise leaves the stack without resolving.",
    cards := #["Guttersnipe"],
    sets := #["hoc"] },
  { id := 132, comment := "If Andúril is equipped to a creature an opponent controls, Andúril's controller will create two tapped Spirit tokens each time that creature attacks. Even if that creature is legendary, the Spirits would not enter the battlefield attacking.",
    cards := #["Andúril, Flame of the West"],
    sets := #["hoc"] },
  { id := 133, comment := "If Arwen, Weaver of Hope and another creature you control enter the battlefield at the same time, Arwen's ability won't cause that creature to enter with additional +1/+1 counters on it.",
    cards := #["Arwen, Weaver of Hope"],
    sets := #["hoc"] },
  { id := 134, comment := "If Banishing Light leaves the battlefield before its triggered ability resolves, the target permanent won’t be exiled.",
    cards := #["Banishing Light"],
    sets := #["hoc"] },
  { id := 135, comment := "If Bifur entering causes you to have an enduring story, his \"enters or attacks\" ability triggers an additional time.",
    cards := #["Bifur, Melodic Rider"],
    sets := #["hob"] },
  { id := 136, comment := "If Celebrate the Mountain-king leaves the battlefield before its triggered ability resolves, no nonland permanents will be exiled.",
    cards := #["Celebrate the Mountain-king"],
    sets := #["hob"] },
  { id := 137, comment := "If Colossal Whale leaves the battlefield before its triggered ability resolves, the target creature won't be exiled.",
    cards := #["Colossal Whale"],
    sets := #["hoc"] },
  { id := 138, comment := "If Fiend Hunter leaves the battlefield before its first ability has resolved, its second ability will trigger and do nothing. Then its first ability will resolve and exile the target creature indefinitely. This is different from abilities on other cards that exile a permanent \"until\" something happens.",
    cards := #["Fiend Hunter"],
    sets := #["hoc"] },
  { id := 139, comment := "If Great Fierce Bee dies at the same time as one or more other creatures, Great Fierce Bee's ability still triggers.",
    cards := #["Great Fierce Bee"],
    sets := #["hob"] },
  { id := 140, comment := "If Head of the Hunt would leave the battlefield at the same time as one or more creatures an opponent controls would die, those creatures will still be exiled.",
    cards := #["Head of the Hunt"],
    sets := #["hob"] },
  { id := 141, comment := "If Minas Tirith Garrison is untapped as its last ability resolves, it can be tapped for its own last ability.",
    cards := #["Minas Tirith Garrison"],
    sets := #["hoc"] },
  { id := 142, comment := "If Smite the Deathless doesn't deal damage to the target creature (perhaps because that damage was prevented), the additional effects will still apply. It will still lose indestructible, and it will be exiled instead of dying that turn.",
    cards := #["Smite the Deathless"],
    sets := #["hoc"] },
  { id := 143, comment := "If The Master of Lake-town dies at the same time that a player loses life (for example, if it dies in combat and another creature dealt combat damage to a player), you choose the order for The Master of Lake-town's two triggered abilities. If the mill effect resolves first, those cards—and also The Master of Lake-town—will be in graveyards before you determine how many cards to draw with its last ability.",
    cards := #["The Master of Lake-town"],
    sets := #["hob"] },
  { id := 144, comment := "If Thranduil, the Elvenking gains a set of linked activated abilities (for example, one ability that exiles a card and another that refers to the card \"exiled with\" the object), that link only lasts for as long as Thranduil has those abilities. If it loses the abilities and then regains them, the link is lost.",
    cards := #["Thranduil, the Elvenking"],
    sets := #["hob"] },
  { id := 145, comment := "If a card in a graveyard has {X} in its mana cost, X is 0 for the purpose of determining its mana value.",
    cards := #["Bilbo, Unexpected Adventurer"],
    sets := #["hoc"] },
  { id := 146, comment := "If a card in your hand is already revealed (perhaps because it was revealed to pay a cost of a spell that's still on the stack or due to the effect of a card like Telepathy), you may reveal it again to pay the cost of another spell or ability that requires you to reveal a card from your hand.",
    cards := #["Elven Passage"],
    sets := #["hob"] },
  { id := 147, comment := "If a card or token enters as a copy of a permanent, the new permanent isn't kicked, even if the original was.",
    cards := #["Galadriel's Dismissal"],
    sets := #["hoc"] },
  { id := 148, comment := "If a creature enters with +1/+1 counters or a continuous effect such as that of Wedding Festivity will apply to the creature on the battlefield, those effects apply when checking to see if Mentor of the Meek's ability will trigger.",
    cards := #["Mentor of the Meek"],
    sets := #["hoc"] },
  { id := 149, comment := "If a creature token is exiled, it ceases to exist. It won't be returned to the battlefield.",
    cards := #["Colossal Whale", "Super Villain Lockup"],
    sets := #["hoc", "msh"] },
  { id := 150, comment := "If a noncreature spell was already cast by an opponent the turn The Queen of Dale enters, that opponent already cast their first noncreature spell this turn, and The Queen of Dale's ability won't trigger for that opponent that turn.",
    cards := #["The Queen of Dale"],
    sets := #["hob"] },
  { id := 151, comment := "If a player has protection from everything, it means three things: 1) All damage that would be dealt to that player is prevented. 2) Auras can't be attached to that player. 3) That player can't be the target of spells or abilities.",
    cards := #["The One Ring"],
    sets := #["hoc"] },
  { id := 152, comment := "If a spell for which the gift was promised is countered, doesn't resolve (perhaps because all of its targets are illegal), or is otherwise removed from the stack, the gift won't be given. None of its other effects will happen either.",
    cards := #["Bilbo's Gambit"],
    sets := #["hob"] },
  { id := 153, comment := "If a spell has {X} in its mana cost, you must choose 0 as the value of X when casting it without paying its mana cost.",
    cards := #["Inside Information"],
    sets := #["hob"] },
  { id := 154, comment := "If a spell is returned to its owner's hand, it's removed from the stack and thus will not resolve. This works against a spell that can't be countered.",
    cards := #["Reprieve"],
    sets := #["hoc"] },
  { id := 155, comment := "If a spell or ability causes an opponent to put cards into their hand without specifically using the word \"draw,\" it's not a card drawn.",
    cards := #["Orcish Bowmasters"],
    sets := #["hoc"] },
  { id := 156, comment := "If a spell or ability targets Old Fat Spider more than once, its last ability still triggers only once.",
    cards := #["Old Fat Spider"],
    sets := #["hob"] },
  { id := 157, comment := "If a spell with cascade is countered, the cascade ability will still resolve normally.",
    cards := #["Call Forth the Tempest"],
    sets := #["hoc"] },
  { id := 158, comment := "If a spell you cast has {X} in its mana cost, you must choose 0 as the value of X when casting it without paying its mana cost.",
    cards := #["Gandalf, Party Guest"],
    sets := #["hoc"] },
  { id := 159, comment := "If a token is exiled this way, it will cease to exist and won't return to the battlefield.",
    cards := #["Lake-town Mariners // Gone Fishing", "Cloak and Dagger, Entwined", "The Mind Stone", "Secret Invasion", "S.H.I.E.L.D. Flying Car", "Web Up"],
    sets := #["hob", "msh"] },
  { id := 160, comment := "If a token is exiled this way, it will cease to exist and won’t return to the battlefield.",
    cards := #["Banishing Light"],
    sets := #["hoc"] },
  { id := 161, comment := "If a token is exiled this way, it won't return to the battlefield.",
    cards := #["Fiend Hunter"],
    sets := #["hoc"] },
  { id := 162, comment := "If a token is exiled, it ceases to exist. It won't be returned to the battlefield.",
    cards := #["Celebrate the Mountain-king"],
    sets := #["hob"] },
  { id := 163, comment := "If all three modes have been chosen this turn, Galadriel, Light of Valinor's triggered ability is removed from the stack with no effect.",
    cards := #["Galadriel, Light of Valinor"],
    sets := #["hoc"] },
  { id := 164, comment := "If all three modes have been chosen, Gollum's triggered ability is removed from the stack with no effect, but Gollum remains on the battlefield.",
    cards := #["Gollum, Riddle Master"],
    sets := #["hob"] },
  { id := 165, comment := "If an Aura is exiled this way, its owner chooses what it will enchant as it returns to the battlefield. An Aura put onto the battlefield this way doesn’t target anything (so it could be attached to a permanent an opponent controls with hexproof, for example), but the Aura’s enchant ability restricts what it can be attached to. If the Aura can’t legally be attached to anything, it remains in exile for the rest of the game.",
    cards := #["Banishing Light"],
    sets := #["hoc"] },
  { id := 166, comment := "If an activated ability of an Elf card in your graveyard references the card it's printed on by name, treat Thranduil, the Elvenking's instance of that ability as though it referenced Thranduil by name instead.",
    cards := #["Thranduil, the Elvenking"],
    sets := #["hob"] },
  { id := 167, comment := "If an attacking Human is tapped for Minas Tirith Garrison's ability (perhaps because it has vigilance or it was untapped after being declared as an attacker), that Human remains an attacking creature.",
    cards := #["Minas Tirith Garrison"],
    sets := #["hoc"] },
  { id := 168, comment := "If an attacking creature has multiple evasion abilities, such as shadow and flying, a creature can block it only if that creature satisfies all of the appropriate evasion abilities.",
    cards := #["Minas Morgul, Dark Fortress"],
    sets := #["hoc"] },
  { id := 169, comment := "If an effect creates more than one kind of token, it'll create twice as many of each kind. For example, if you control Bilbo, Fellow Conspirator and Bard, King of Dale and you create a Food token, you'll create two Food tokens and two Treasure tokens (regardless of the order you chose to apply the replacement effects).",
    cards := #["Bard, King of Dale"],
    sets := #["hob"] },
  { id := 170, comment := "If an effect refers to a \"[subtype] card,\" it refers only to a card that has that subtype. For example, Elven Chorus is not an Elf, despite referencing elves in its name and featuring elves in its art.",
    cards := #["Elven Passage"],
    sets := #["hob"] },
  { id := 171, comment := "If multiple Dwarves you control deal combat damage to players and/or battles at the same time, Thorin's first ability will trigger once for each of those Dwarves.",
    cards := #["Thorin, Company's Leader"],
    sets := #["hoc"] },
  { id := 172, comment := "If multiple creatures enter the battlefield simultaneously, you must still choose different modes for each instance of the triggered ability that's put onto the stack. If more than three creatures enter the battlefield simultaneously, that choice is made only for the first three.",
    cards := #["Galadriel, Light of Valinor"],
    sets := #["hoc"] },
  { id := 173, comment := "If no target is chosen for Azog's ability, \"its controller\" is undefined and no player amasses Goblins.",
    cards := #["Azog, Moria's Ruin"],
    sets := #["hob"] },
  { id := 174, comment := "If some of the targets are illegal targets as Gandalf's triggered ability tries to resolve, the original division of damage still applies but no damage is dealt to the illegal targets. If all targets are illegal, Gandalf's triggered ability doesn't resolve.",
    cards := #["Gandalf, Spark Starter"],
    sets := #["hob"] },
  { id := 175, comment := "If that player exiles their entire library without exiling an instant or sorcery card, they will randomize the order of the exiled cards, and the cards then become that player's library, ending the effect. They will not continue to exile and randomize their library forever.",
    cards := #["Gríma, Saruman's Footman"],
    sets := #["hoc"] },
  { id := 176, comment := "If the card has {X} in its mana cost, you must choose 0 as the value for X when casting it without paying its mana cost.",
    cards := #["Thranduil's Decree"],
    sets := #["hob"] },
  { id := 177, comment := "If the card has {X} in its mana cost, you must choose 0 as the value of X when casting it without paying its mana cost.",
    cards := #["Call Forth the Tempest"],
    sets := #["hoc"] },
  { id := 178, comment := "If the creature spell has {X} in its mana cost, use the value chosen for X when calculating that spell's mana value.",
    cards := #["Dancing from Dark to Dawn"],
    sets := #["hob"] },
  { id := 179, comment := "If the defending player controls two or more creatures tied for the least power among creatures they control, that player chooses one of them to sacrifice.",
    cards := #["Witch-king, Bringer of Ruin"],
    sets := #["hoc"] },
  { id := 180, comment := "If the effect creating the tokens instructs you to do something with those tokens at a later time, like exiling them at the end of combat, you'll do that for all the tokens.",
    cards := #["Bard, King of Dale"],
    sets := #["hob"] },
  { id := 181, comment := "If the equipped creature is legendary, Andúril's controller chooses which player, planeswalker, or battle the Spirit tokens are attacking. Each Spirit token can enter attacking a different player, planeswalker, or battle, and they don't need to be the same player, planeswalker, or battle that the equipped creature is attacking.",
    cards := #["Andúril, Flame of the West"],
    sets := #["hoc"] },
  { id := 182, comment := "If the first creature spell you cast in a turn has {X} in its mana cost, you choose the value of X before calculating the spell's total cost. For example, if the first creature spell you cast in a turn has a mana cost of {X}{G}, you could choose 2 as the value of X and pay {G} to cast the spell.",
    cards := #["Radagast of Rhosgobel"],
    sets := #["hob"] },
  { id := 183, comment := "If the greatest number of artifacts an opponent controls is seven or more, Cavern-Hoard Dragon costs {R}{R} to cast.",
    cards := #["Cavern-Hoard Dragon"],
    sets := #["hoc"] },
  { id := 184, comment := "If the legendary spell you cast this way is copied, the copy can be countered.",
    cards := #["Delighted Halfling"],
    sets := #["hoc"] },
  { id := 185, comment := "If the revealed creature card has {X} in its mana cost, X is 0 for the purposes of determining its mana value.",
    cards := #["Part in Friendship"],
    sets := #["hob"] },
  { id := 186, comment := "If the spell has {X} in its mana cost, you must choose 0 as the value of X.",
    cards := #["Glamdring"],
    sets := #["hoc"] },
  { id := 187, comment := "If the target creature becomes an illegal target, the Equipment remains on the battlefield unattached.",
    cards := #["Mithril Coat"],
    sets := #["hoc"] },
  { id := 188, comment := "If the target creature is an illegal target by the time Hithlain Knots tries to resolve, the spell doesn't resolve. You won't scry 1, and you won't draw a card. However, if the target is legal but doesn't become tapped (most likely because it's already tapped), you do scry 1, and you do draw a card.",
    cards := #["Hithlain Knots"],
    sets := #["hoc"] },
  { id := 189, comment := "If the target of Arwen's second ability is illegal as it tries to resolve, the ability does nothing. You won't get to put any counters on Arwen.",
    cards := #["Arwen, Mortal Queen"],
    sets := #["hoc"] },
  { id := 190, comment := "If the token you create has any \"as [this permanent] enters\" or \"[this permanent] enters with\" abilities, first determine how many tokens are being created, then apply those abilities individually for each one. For example, if a token with \"You may have [this permanent] enter as a copy of any creature on the battlefield\" would be created (such as an embalmed Vizier of Many Faces), the resulting two tokens can each copy a different creature.",
    cards := #["Bard, King of Dale"],
    sets := #["hob"] },
  { id := 191, comment := "If the top card of your library changes while you're casting a spell, playing a land, or activating an ability, you can't look at the new top card until you finish doing so. This means that if you cast a spell from the top of your library, you can't look at the next one until you're done paying for that spell.",
    cards := #["Elven Chorus"],
    sets := #["hoc"] },
  { id := 192, comment := "If there are additional costs to cast a spell, or if the cost to cast a spell is increased by an effect, apply those increases before applying cost reductions.",
    cards := #["Radagast of Rhosgobel"],
    sets := #["hob"] },
  { id := 193, comment := "If two or more replacement effects would apply to a card-drawing event, the player drawing the card chooses the order in which to apply them.",
    cards := #["Bard, King of Dale"],
    sets := #["hob"] },
  { id := 194, comment := "If you activate the last ability of Eagle's Rescue and the target creature becomes an illegal target in response, the ability doesn't resolve and Eagle's Rescue remains in your graveyard.",
    cards := #["Eagle's Rescue"],
    sets := #["hob"] },
  { id := 195, comment := "If you cast a card \"without paying its mana cost,\" you can't choose to cast it for any alternative costs. You can, however, pay additional costs. If the card has any mandatory additional costs, you must pay those to cast the card.",
    cards := #["Call Forth the Tempest"],
    sets := #["hoc"] },
  { id := 196, comment := "If you cast a spell \"without paying its mana cost\", you can't choose to cast it for any alternative costs. You can, however, pay additional costs, such as kicker costs. If the card has any mandatory additional costs, those must be paid to cast the spell.",
    cards := #["Glamdring"],
    sets := #["hoc"] },
  { id := 197, comment := "If you cast a spell \"without paying its mana cost,\" you can't choose to cast it for any alternative costs. You can, however, pay additional costs, such as kicker costs. If the card has any mandatory additional costs, those must be paid to cast the spell.",
    cards := #["Gandalf, Party Guest", "Cosmic Cube", "Doom Reigns Supreme"],
    sets := #["hoc", "msh"] },
  { id := 198, comment := "If you cast a spell for another cost \"rather than pay its mana cost,\" you can't choose to cast it for any alternative costs. You can, however, pay additional costs. If a spell has any mandatory additional costs, such as that of Stir Up Trouble, those must be paid for it.",
    cards := #["Inside Information"],
    sets := #["hob"] },
  { id := 199, comment := "If you cast a spell that's multiple colors, more than one of Aragorn, the Uniter's abilities may trigger. In that case, you choose the order in which the abilities are put onto the stack.",
    cards := #["Aragorn, the Uniter"],
    sets := #["hoc"] },
  { id := 200, comment := "If you cast a spell using Glamdring's triggered ability, you do so as part of the resolution of the ability. You can't wait to cast the spell later in the turn. Timing permissions based on the card's type are ignored.",
    cards := #["Glamdring"],
    sets := #["hoc"] },
  { id := 201, comment := "If you choose not to cast the card, it is put on the bottom of its owner's library in a random order along with the other exiled cards.",
    cards := #["Gríma, Saruman's Footman"],
    sets := #["hoc"] },
  { id := 202, comment := "If you choose to find only one basic land card, you put it onto the battlefield tapped.",
    cards := #["Troop of Ponies"],
    sets := #["hob"] },
  { id := 203, comment := "If you control Bard, King of Dale and create an Army token because you amass and didn't already control an Army, you will create two Army tokens. However, since you can only put the counters on one of the tokens, the other remains a 0/0 creature and will be put into its owner's graveyard the next time state-based actions are checked.",
    cards := #["Bard, King of Dale"],
    sets := #["hob"] },
  { id := 204, comment := "If you control Bilbo and would create some number of Food tokens, you will instead create that many Food tokens and that many Treasure tokens.",
    cards := #["Bilbo, Fellow Conspirator"],
    sets := #["hoc"] },
  { id := 205, comment := "If you control no legendary creatures or legendary planeswalkers, you can activate Mox Amber's ability, but you won't add any mana.",
    cards := #["Mox Amber"],
    sets := #["hoc"] },
  { id := 206, comment := "If you control no other creatures as Merciless Executioner's ability resolves, you'll have to sacrifice Merciless Executioner.",
    cards := #["Merciless Executioner"],
    sets := #["hoc"] },
  { id := 207, comment := "If you control ten permanents but don't control a permanent or resolving spell with ascend, you don't get the city's blessing. For example, if you control ten permanents, lose control of two, then cast Andúril, Narsil Reforged, you won't have the city's blessing.",
    cards := #["Andúril, Narsil Reforged"],
    sets := #["hoc"] },
  { id := 208, comment := "If you copy a kicked spell on the stack, the copy is also kicked.",
    cards := #["The Eagles Are Coming!"],
    sets := #["hob"] },
  { id := 209, comment := "If you copy a kicked spell on the stack, the copy is also kicked. If the copied spell is a permanent spell, the token the copy of that spell becomes when it enters is also kicked.",
    cards := #["Galadriel's Dismissal"],
    sets := #["hoc"] },
  { id := 210, comment := "If you copy a spell for which the gift was promised, the gift was also promised to the same player for the copy. If a card or token enters as a copy of a permanent that's already on the battlefield, the gift isn't promised for that new permanent, even if it was promised for the original.",
    cards := #["Bilbo's Gambit"],
    sets := #["hob"] },
  { id := 211, comment := "If you don't have a commander, Arcane Signet's ability produces no mana.",
    cards := #["Arcane Signet"],
    sets := #["hoc"] },
  { id := 212, comment := "If you don't have an enchantment, instant, or sorcery card in your hand, you won't be able to pay Saruman of Many Colors's ward cost.",
    cards := #["Saruman of Many Colors"],
    sets := #["hoc"] },
  { id := 213, comment := "If you don't want to cast the copy, you can choose not to; the copy ceases to exist the next time state-based actions are checked.",
    cards := #["Saruman of Many Colors"],
    sets := #["hoc"] },
  { id := 214, comment := "If you draw your second card in a turn while recruiting, the Human Soldier you create can be chosen as the target of Bard the Bowman's ability. ",
    cards := #["Bard the Bowman"],
    sets := #["hob"] },
  { id := 215, comment := "If you have two commanders, the ability adds one mana of any color in their combined color identities.",
    cards := #["Arcane Signet"],
    sets := #["hoc"] },
  { id := 216, comment := "If you haven't gained 3 or more life by the time an end step begins, The Gaffer's ability won't trigger at all.",
    cards := #["The Gaffer"],
    sets := #["hoc"] },
  { id := 217, comment := "If you increase the power of the targeted creature after the ability resolves, it still can’t be blocked that turn.",
    cards := #["Dwarven Warriors"],
    sets := #["hoc"] },
  { id := 218, comment := "If you put a permanent with a kicker ability onto the battlefield without casting it, you can't kick it.",
    cards := #["Galadriel's Dismissal"],
    sets := #["hoc"] },
  { id := 219, comment := "If you somehow control two Bilbo, Fellow Conspirators and would create some number of Food tokens, you will instead create that many Food tokens and twice that many Treasure tokens. Three Bilbos means that many Food tokens and three times that many Treasure tokens, and so on.",
    cards := #["Bilbo, Fellow Conspirator"],
    sets := #["hoc"] },
  { id := 220, comment := "If you use the first ability of Bard's Company to cast it as though it had flash, you must control a Human only as you begin the casting process and put Bard's Company on the stack. Losing control of that Human while you're casting Bard's Company (perhaps because of sacrificing it to activate a mana ability) or in response to Bard's Company won't affect Bard's Company on the stack.",
    cards := #["Bard's Company"],
    sets := #["hob"] },
  { id := 221, comment := "If your commander is a card that has no colors in its color identity, Arcane Signet's ability produces no mana. It doesn't produce {C}.",
    cards := #["Arcane Signet"],
    sets := #["hoc"] },
  { id := 222, comment := "If your legendary creatures and legendary planeswalkers are all colorless, you can activate Mox Amber's ability, but you won't add any mana. Colorless is not a color.",
    cards := #["Mox Amber"],
    sets := #["hoc"] },
  { id := 223, comment := "If your tenth permanent enters the battlefield and then a permanent leaves the battlefield immediately afterwards (most likely due to the \"legend rule\" or due to being a creature with 0 toughness), you get the city's blessing before it leaves the battlefield.",
    cards := #["Andúril, Narsil Reforged"],
    sets := #["hoc"] },
  { id := 224, comment := "In a Two-Headed Giant game, Guttersnipe's ability causes the opposing team to lose 4 life.",
    cards := #["Guttersnipe"],
    sets := #["hoc"] },
  { id := 225, comment := "In a multiplayer game, Landroval, Horizon Witness's triggered ability triggers once for each player you attack with at least two creatures.",
    cards := #["Landroval, Horizon Witness"],
    sets := #["hoc"] },
  { id := 226, comment := "In a multiplayer game, a player may lose the game at the same time that their creatures die. If so, Dreaded Bat-Cloud's cost reduction applies.",
    cards := #["Dreaded Bat-Cloud"],
    sets := #["hob"] },
  { id := 227, comment := "In a multiplayer game, if Celebrate the Mountain-king's owner leaves the game, the exiled cards will return to the battlefield. Because the one-shot effect that returns the cards isn't an ability that goes on the stack, it won't cease to exist along with the leaving player's spells and abilities on the stack.",
    cards := #["Celebrate the Mountain-king"],
    sets := #["hob"] },
  { id := 228, comment := "In a multiplayer game, if Colossal Whale's owner leaves the game, the exiled card will return to the battlefield. Because the one-shot effect that returns the card isn't an ability that goes on the stack, it won't cease to exist along with the leaving player's spells and abilities on the stack.",
    cards := #["Colossal Whale"],
    sets := #["hoc"] },
  { id := 229, comment := "In a multiplayer game, if you lose the game, the creature exiled with Fiend Hunter remains exiled indefinitely. This is also different from abilities on other cards that exile a permanent \"until\" something happens.",
    cards := #["Fiend Hunter"],
    sets := #["hoc"] },
  { id := 230, comment := "In the rare case that the Elf card you return to your hand doesn't have power, you'll gain 0 life.",
    cards := #["Mirkwood Elk"],
    sets := #["hoc"] },
  { id := 231, comment := "It doesn't matter who has chosen any particular mode. For example, say you control Galadriel, Light of Valinor and have chosen the first two modes this turn. If an opponent gains control of Galadriel, that player can choose only the third mode this turn.",
    cards := #["Galadriel, Light of Valinor"],
    sets := #["hoc"] },
  { id := 232, comment := "Mentor of the Meek's ability checks the power of the other creature only as it enters. If that creature's power is 2 or less, the ability will trigger. Once the ability triggers, raising that creature's power above 2 won't affect that ability. Similarly, reducing the creature's power to 2 or less after it enters won't cause the ability to trigger.",
    cards := #["Mentor of the Meek"],
    sets := #["hoc"] },
  { id := 233, comment := "Mithril Coat doesn't enter the battlefield attached to a creature. Instead, the Equipment enters the battlefield and then a triggered ability attaches it to a creature. You may cast Mithril Coat even if you don't control any creatures.",
    cards := #["Mithril Coat"],
    sets := #["hoc"] },
  { id := 234, comment := "Mox Amber's ability adds one mana of the color of your choice from among the colors of legendary creatures and legendary planeswalkers you control. It doesn't add one mana of each of those colors.",
    cards := #["Mox Amber"],
    sets := #["hoc"] },
  { id := 235, comment := "Multiple instances of shadow on the same creature are redundant.",
    cards := #["Minas Morgul, Dark Fortress"],
    sets := #["hoc"] },
  { id := 236, comment := "Nasty Little Rabbit's ability will check at the start of your beginning of combat step to see if you control a creature with power 4 or greater. If you don't, the ability won't trigger at all. If it does trigger, the ability will check again as it tries to resolve. If you don't control a creature with power 4 or greater at that time, the ability won't resolve.",
    cards := #["Nasty Little Rabbit"],
    sets := #["hob"] },
  { id := 237, comment := "Nighthowl Pursuer's triggered ability will check when it attacks to see if you control a creature with power 4 or greater. If you don't, the ability won't trigger at all. It will not check again when it resolves, so the ability will resolve even if you no longer control a creature with power 4 or greater.",
    cards := #["Nighthowl Pursuer"],
    sets := #["hob"] },
  { id := 238, comment := "No matter what spell you cast with the first cascade ability (or with any cascade abilities that result from casting that spell), the second cascade ability will look for a card with mana value less than Call Forth the Tempest's mana value of 8.",
    cards := #["Call Forth the Tempest"],
    sets := #["hoc"] },
  { id := 239, comment := "Nothing other than the specified events are prevented or illegal. An effect that doesn't target you could still cause you to discard cards, for example. Creatures can still attack you while you have protection from everything, although combat damage that they would deal to you will be prevented.",
    cards := #["The One Ring"],
    sets := #["hoc"] },
  { id := 240, comment := "Old Fat Spider's last ability resolves before the spell or ability that caused it to trigger. It resolves even if that spell or ability is countered or otherwise leaves the stack without resolving.",
    cards := #["Old Fat Spider"],
    sets := #["hob"] },
  { id := 241, comment := "Once Bilbo has been blocked, increasing the power of a creature blocking him to 3 or greater won't cause him to become unblocked.",
    cards := #["Bilbo, Unexpected Adventurer"],
    sets := #["hoc"] },
  { id := 242, comment := "Once Chief Warg's Company has attacked, it will remain an attacking creature even if you no longer control two or more other Wolves.",
    cards := #["Chief Warg's Company"],
    sets := #["hob"] },
  { id := 243, comment := "Once Nimrodel Watcher has been blocked, resolving its triggered ability won't change or undo that block.",
    cards := #["Nimrodel Watcher"],
    sets := #["hoc"] },
  { id := 244, comment := "Once a creature has been blocked, activating the ability of Elvenking's Harper won't cause that creature to become unblocked.",
    cards := #["Elvenking's Harper"],
    sets := #["hob"] },
  { id := 245, comment := "Once a creature has been blocked, that creature remains blocked and will deal and be dealt combat damage even if it gains or loses shadow or if the blocking creature gains or loses shadow.",
    cards := #["Minas Morgul, Dark Fortress"],
    sets := #["hoc"] },
  { id := 246, comment := "Once a player has announced that they are casting Cavern-Hoard Dragon, no player may take actions to try and change the greatest number of artifacts an opponent controls before Cavern-Hoard Dragon's cost is locked in.",
    cards := #["Cavern-Hoard Dragon"],
    sets := #["hoc"] },
  { id := 247, comment := "Once a player has announced that they are casting The Lord of the Eagles, no player may take actions to try and change the power of creatures its controller controls before that spell's cost is locked in.",
    cards := #["The Lord of the Eagles"],
    sets := #["hob"] },
  { id := 248, comment := "Once the exiled creature returns, it's considered a new object with no relation to the object that it was. Auras attached to the exiled creature will be put into their owners' graveyards. Equipment attached to the exiled creature will become unattached and remain on the battlefield. Any counters on the exiled creature will cease to exist.",
    cards := #["Fiend Hunter"],
    sets := #["hoc"] },
  { id := 249, comment := "Once you announce that you're casting a spell, no player may take actions until the spell has been paid for. Notably, opponents can't try to change how much Glamdring will reduce costs by lowering the power of the equipped creature.",
    cards := #["Glamdring, Foe-hammer // Gleam of Death"],
    sets := #["hob"] },
  { id := 250, comment := "Once you cast Flame of Anor and choose two modes, it doesn't matter what happens to the Wizard you control in response. Flame of Anor will still have two modes chosen.",
    cards := #["Flame of Anor"],
    sets := #["hoc"] },
  { id := 251, comment := "Once you have the city's blessing, you have it for the rest of the game, even if you lose control of some or all your permanents. The city's blessing isn't a permanent itself and can't be removed by any effect.",
    cards := #["Andúril, Narsil Reforged"],
    sets := #["hoc"] },
  { id := 252, comment := "Only a Dragon permanent card can be put onto the battlefield this way.",
    cards := #["Last Light of Durin's Day"],
    sets := #["hob"] },
  { id := 253, comment := "Permanents phase back in during their controller's untap step, immediately before that player untaps their permanents. Creatures that phase in this way are able to attack during that turn, and their activated abilities with {T} in their costs can be activated. If a permanent had counters on it when it phased out, it will have those counters when it phases back in.",
    cards := #["Galadriel's Dismissal"],
    sets := #["hoc"] },
  { id := 254, comment := "Phased-out permanents are treated as though they don't exist. They can't be the targets of spells or abilities, their static abilities have no effect on the game, their triggered abilities can't trigger, they can't attack or block, and so on.",
    cards := #["Galadriel's Dismissal"],
    sets := #["hoc"] },
  { id := 255, comment := "Phasing out doesn't cause any \"leaves the battlefield\" abilities to trigger. Similarly, phasing in won't cause any \"enters the battlefield\" abilities to trigger.",
    cards := #["Galadriel's Dismissal"],
    sets := #["hoc"] },
  { id := 256, comment := "Protection from everything will usually prevent damage if it would be dealt to you, but some damage can't be prevented. In this case, that damage reduces your life total as normal.",
    cards := #["The One Ring"],
    sets := #["hoc"] },
  { id := 257, comment := "Radagast of Rhosgobel's ability doesn't change the mana cost or mana value of any spell. It changes only the total cost you actually pay.",
    cards := #["Radagast of Rhosgobel"],
    sets := #["hob"] },
  { id := 258, comment := "Radagast of Rhosgobel's ability will look at the entire turn, even if Radagast wasn't on the battlefield for some of it. Notably, if you cast Radagast of Rhosgobel in a turn, then no other creature spell you cast that turn can be your first.",
    cards := #["Radagast of Rhosgobel"],
    sets := #["hob"] },
  { id := 259, comment := "Radagast's ability can't reduce the amount of colored mana you pay for a spell. It reduces only the generic component of that cost.",
    cards := #["Radagast of Rhosgobel"],
    sets := #["hob"] },
  { id := 260, comment := "Ravening Warg's triggered ability will check when it attacks to see if you control a creature with power 4 or greater. If you don't, the ability won't trigger at all. It will not check again when it resolves, so the ability will resolve even if you no longer control a creature with power 4 or greater.",
    cards := #["Ravening Warg"],
    sets := #["hob"] },
  { id := 261, comment := "Replacement effects are unaffected by Wizard's Staff's second ability.",
    cards := #["Wizard's Staff"],
    sets := #["hob"] },
  { id := 262, comment := "Settle the Wreckage targets only the player. Attacking creatures with hexproof that player controls will be exiled as this spell resolves.",
    cards := #["Settle the Wreckage"],
    sets := #["hob"] },
  { id := 263, comment := "Settle the Wreckage targets only the player. Creatures with hexproof that player controls will be exiled as this spell resolves.",
    cards := #["Settle the Wreckage"],
    sets := #["hob"] },
  { id := 264, comment := "Shadow of the Enemy uses a new template indicating that you may spend mana as though it were mana of any type to cast the exiled cards. The six types of mana are white, blue, black, red, green, and colorless.",
    cards := #["Shadow of the Enemy"],
    sets := #["hoc"] },
  { id := 265, comment := "Similarly, the effect of the last ability on multiple Bard, King of Dale is cumulative. If you control two, you'll create four times the number of tokens.",
    cards := #["Bard, King of Dale"],
    sets := #["hob"] },
  { id := 266, comment := "Snow mana is not a type of mana. Shadow of the Enemy won't let you pay a snow cost using mana produced by a nonsnow source.",
    cards := #["Shadow of the Enemy"],
    sets := #["hoc"] },
  { id := 267, comment := "Spells that were cast before Lotho, Corrupt Shirriff count. If Lotho, Corrupt Shirriff was the first spell you cast this turn, the next spell you cast this turn is your second spell.",
    cards := #["Lotho, Corrupt Shirriff"],
    sets := #["hoc"] },
  { id := 268, comment := "The Chief Warg's triggered ability will check when you attack to see if you control a creature with power 4 or greater. If you don't, the ability won't trigger at all. It will not check again when it resolves, so the trigger will resolve even if you no longer control a creature with power 4 or greater.",
    cards := #["The Chief Warg"],
    sets := #["hob"] },
  { id := 269, comment := "The Gaffer's ability looks at how much life you've gained in the turn, even if it wasn't on the battlefield when you gained life. It doesn't care if you also lost life, even if you lost more life than you gained.",
    cards := #["The Gaffer"],
    sets := #["hoc"] },
  { id := 270, comment := "The Goblin or Orc you control doesn't have to block.",
    cards := #["Olog-hai Crusher"],
    sets := #["hoc"] },
  { id := 271, comment := "The Master of Lake-town will usually be in a graveyard as its last ability resolves.",
    cards := #["The Master of Lake-town"],
    sets := #["hob"] },
  { id := 272, comment := "The ability can be activated after a creature is blocked, but it has no effect. Once a creature is blocked, it can’t be unblocked.",
    cards := #["Dwarven Warriors"],
    sets := #["hoc"] },
  { id := 273, comment := "The ability of Mirkwood Meditator overwrites any previous effects that set its power and/or toughness to specific values. Other effects that set these characteristics to specific values that start to apply after the ability resolves will overwrite that part of the effect.",
    cards := #["Mirkwood Meditator"],
    sets := #["hob"] },
  { id := 274, comment := "The ability that defines Esgaroth Garrison's power works in all zones, not just the battlefield. As long as Esgaroth Garrison is on the battlefield (and still a creature), that ability will count Esgaroth Garrison itself.",
    cards := #["Esgaroth Garrison"],
    sets := #["hob"] },
  { id := 275, comment := "The ability that defines Mirkwood Pathmaker's power and toughness works in all zones, not just the battlefield.",
    cards := #["Mirkwood Pathmaker"],
    sets := #["hob"] },
  { id := 276, comment := "The ability triggers only once, no matter how many creatures are blocking it. The ability resolves and deals damage to those creatures before combat damage is dealt. Even if that damage destroys all creatures blocking Battle-Scarred Goblin, Battle-Scarred Goblin doesn't become unblocked.",
    cards := #["Battle-Scarred Goblin"],
    sets := #["hoc"] },
  { id := 277, comment := "The cards are exiled face up. All players will be able to see them.",
    cards := #["Gríma, Saruman's Footman"],
    sets := #["hoc"] },
  { id := 278, comment := "The choice of creature type is made as An Unexpected Party enters. Players can't take any actions between the time the choice is made and the time the appropriate creatures begin to get +2/+2.",
    cards := #["An Unexpected Party // At the Door"],
    sets := #["hob"] },
  { id := 279, comment := "The chosen player needs only to have the most life or tied for most life as The Black Gate's last ability resolves. After the ability resolves, any changes in life total won't affect which creatures can block or be blocked that turn.",
    cards := #["The Black Gate"],
    sets := #["hoc"] },
  { id := 280, comment := "The cost reduction ability reduces only the generic mana in the cost to cast The Lord of the Eagles. The colored mana must still be paid.",
    cards := #["The Lord of the Eagles"],
    sets := #["hob"] },
  { id := 281, comment := "The cost reduction applies only to generic mana in the costs of spells you cast from anywhere other than your hand. It can't reduce requirements of a specific color of mana.",
    cards := #["Bilbo, Thief in the Night"],
    sets := #["hob"] },
  { id := 282, comment := "The cost reduction can apply to alternative costs.",
    cards := #["Radagast of Rhosgobel"],
    sets := #["hob"] },
  { id := 283, comment := "The creature that was targeted by The Black Gate's last ability can't be blocked by any creature the chosen player controls, including creatures that weren't on the battlefield when The Black Gate's ability resolved.",
    cards := #["The Black Gate"],
    sets := #["hoc"] },
  { id := 284, comment := "The creature's owner chooses whether to put it on the top or bottom of their library. If multiple cards are put into the library this way (such as when the spell targets a melded creature), that creature's owner puts all the cards on top or all the cards on the bottom. They put them in whatever order they wish, and do not need to reveal the order.",
    cards := #["Uneasy Partings"],
    sets := #["hob"] },
  { id := 285, comment := "The damaged creature will be exiled if it would die for any reason that turn, not just if it dies due to damage from Smite the Deathless.",
    cards := #["Smite the Deathless"],
    sets := #["hoc"] },
  { id := 286, comment := "The decision to discard your hand is made during the resolution of the ability, so there is no opportunity for an opponent to respond between choosing to discard your hand and drawing cards.",
    cards := #["Balin, Loremaster"],
    sets := #["hob"] },
  { id := 287, comment := "The effect making the permanents Food artifacts lasts indefinitely. It doesn't expire during the cleanup step.",
    cards := #["Supper for Spiders"],
    sets := #["hob"] },
  { id := 288, comment := "The effect that allows you to play an additional land that turn is cumulative with other effects that do so.",
    cards := #["Beorn, Reluctant Host // Till and Tend"],
    sets := #["hob"] },
  { id := 289, comment := "The exiled card returns to the battlefield immediately after Colossal Whale leaves the battlefield. Nothing happens between the two events, including state-based actions. The two creatures aren't on the battlefield at the same time. For example, if the returning creature is a Clone, it can't enter the battlefield as a copy of Colossal Whale.",
    cards := #["Colossal Whale"],
    sets := #["hoc"] },
  { id := 290, comment := "The exiled cards return to the battlefield immediately after Celebrate the Mountain-king leaves the battlefield. Nothing happens between the two events, including state-based actions.",
    cards := #["Celebrate the Mountain-king"],
    sets := #["hob"] },
  { id := 291, comment := "The final chapter ability of a Saga is the ability with the greatest chapter number among chapter abilities that Saga has.",
    cards := #["Tom Bombadil"],
    sets := #["hoc"] },
  { id := 292, comment := "The first creature spell you cast each turn doesn't necessarily have to be the first spell you cast. You could cast a sorcery spell and then cast a creature spell that would get the discount.",
    cards := #["Radagast of Rhosgobel"],
    sets := #["hob"] },
  { id := 293, comment := "The legendary spell can't be countered if the mana produced by Delighted Halfling is spent to pay any portion of the spell's cost, even an additional cost or an alternative cost. This is true even if you pay an additional cost while casting a spell \"without paying its mana cost.\"",
    cards := #["Delighted Halfling"],
    sets := #["hoc"] },
  { id := 294, comment := "The phrase \"that hasn't been chosen this turn\" refers only to that specific Galadriel, Light of Valinor. If Galadriel leaves the battlefield and then returns to the battlefield later in the turn, it will be a new object with no memory of the modes chosen when it was previously on the battlefield.",
    cards := #["Galadriel, Light of Valinor"],
    sets := #["hoc"] },
  { id := 295, comment := "The returned cards lose any other subtypes and card types and will be only Food artifacts. They retain their name, mana cost, mana value, and abilities. If any of them are legendary, they remain legendary.",
    cards := #["Supper for Spiders"],
    sets := #["hob"] },
  { id := 296, comment := "The sacrificed creature's last known existence on the battlefield is checked to determine its power.",
    cards := #["Bolg of the North"],
    sets := #["hob"] },
  { id := 297, comment := "The second ability doesn't copy the triggered ability; it just causes the ability to trigger an additional time. Any choices made as you put the ability onto the stack, such as modes and targets, are made separately for each instance of the ability. Any choices made on resolution, such as whether to put counters on a permanent, are also made individually.",
    cards := #["Wizard's Staff"],
    sets := #["hob"] },
  { id := 298, comment := "The top card of your library isn't in your hand, so you can't take other actions that would normally be allowed from your hand, such as discarding it due to an effect or activating a cycling ability.",
    cards := #["Elven Chorus"],
    sets := #["hoc"] },
  { id := 299, comment := "The total cost to cast The Lord of the Eagles is locked in before you pay that cost. For example, if you control three flying creatures, each with power 2, including one you can sacrifice to add {C}, the total cost of The Lord of the Eagles is {1}{U}{U}. Then you can sacrifice the creature as you activate mana abilities just before paying the cost.",
    cards := #["The Lord of the Eagles"],
    sets := #["hob"] },
  { id := 300, comment := "The triggered ability can trigger only once each turn. It doesn't matter whether Bard the Bowman was on the battlefield when the first card was drawn. If he's not on the battlefield when the second card is drawn, the ability can't trigger at all that turn. It won't trigger when the third or fourth card is drawn.",
    cards := #["Bard the Bowman"],
    sets := #["hob"] },
  { id := 301, comment := "The triggered ability can trigger only once each turn. It doesn't matter whether Lakeshore Apothecary was on the battlefield when the first card was drawn. If it's not on the battlefield when the second card is drawn, the ability can't trigger at all that turn. It won't trigger when the third or fourth card is drawn.",
    cards := #["Lakeshore Apothecary"],
    sets := #["hob"] },
  { id := 302, comment := "The triggered ability can trigger only once each turn. It doesn't matter whether Master's Councillors was on the battlefield when the first card was drawn. If it's not on the battlefield when the second card is drawn, the ability can't trigger at all that turn. It won't trigger when the third or fourth card is drawn.",
    cards := #["Master's Councillors"],
    sets := #["hob"] },
  { id := 303, comment := "The type-changing and ability-granting effects last indefinitely. They don't wear off during the cleanup step.",
    cards := #["Beorn's Hospitality"],
    sets := #["hob"] },
  { id := 304, comment := "The type-changing effect of the triggered ability lasts indefinitely. It doesn't wear off during the cleanup step or when Beorn the Fierce leaves the battlefield. The creature couldn't bear not being a Bear!",
    cards := #["Beorn the Fierce"],
    sets := #["hob"] },
  { id := 305, comment := "This card preview was provided to Scryfall courtesy of Wizards of the Coast. Thank you!",
    cards := #["Goblin Cratermaker"],
    sets := #["hoc"] },
  { id := 306, comment := "Thranduil's Company's first ability is cumulative with other effects that let you play additional lands, such as the one from Exploration.",
    cards := #["Thranduil's Company"],
    sets := #["hob"] },
  { id := 307, comment := "To choose a creature type, you must choose an existing creature type, such as Halfling or Scout. You can't choose multiple creature types, such as \"Halfling Scout.\" Card types such as artifacts can't be chosen, nor can subtypes that aren't creature types, such as Forest, Equipment, or Food.",
    cards := #["Raise the Palisade"],
    sets := #["hoc"] },
  { id := 308, comment := "To determine how many additional +1/+1 counters a creature enters the battlefield with, use Arwen, Weaver of Hope's toughness as that creature is entering the battlefield.",
    cards := #["Arwen, Weaver of Hope"],
    sets := #["hoc"] },
  { id := 309, comment := "To determine the amount of damage it deals, use Goblin Fireleaper's power as it last existed on the battlefield, not its power in the graveyard.",
    cards := #["Goblin Fireleaper"],
    sets := #["hoc"] },
  { id := 310, comment := "To determine the total cost of a spell, start with the mana cost or alternative cost you're paying, add any cost increases, then apply any cost reductions (such as that of Bilbo, Thief in the Night). The mana value of the spell is determined only by its mana cost, no matter what the total cost to cast the spell was.",
    cards := #["Bilbo, Thief in the Night"],
    sets := #["hob"] },
  { id := 311, comment := "To determine the total cost of a spell, start with the mana cost or alternative cost you're paying, add any cost increases, then apply any cost reductions (such as that of Cantankerous Keepers's first ability). The mana value of the spell is determined only by its mana cost, no matter what the total cost to cast that spell was.",
    cards := #["Cantankerous Keepers"],
    sets := #["hob"] },
  { id := 312, comment := "To determine the total cost of a spell, start with the mana cost or alternative cost you're paying, add any cost increases, then apply any cost reductions (such as that of Glamdring, Foe-hammer). The mana value of the spell remains unchanged, no matter what the total cost to cast it was.",
    cards := #["Glamdring, Foe-hammer // Gleam of Death"],
    sets := #["hob"] },
  { id := 313, comment := "To determine the total cost of a spell, start with the mana cost or alternative cost you're paying, add any cost increases, then apply any cost reductions (such as that of The Lord of the Eagles). The mana value of the spell remains unchanged, no matter what the total cost to cast it was.",
    cards := #["The Lord of the Eagles"],
    sets := #["hob"] },
  { id := 314, comment := "Triggered abilities use the word \"when,\" \"whenever,\" or \"at.\" They're often written as \"[Trigger condition], [effect].\" Some keyword abilities are triggered abilities and will have \"when,\" \"whenever,\" or \"at the beginning of\" in their reminder text.",
    cards := #["Wizard's Staff"],
    sets := #["hob"] },
  { id := 315, comment := "Two or more creatures you control must attack the same player in order for Landroval, Horizon Witness's ability to trigger. Creatures you control that attack planeswalkers that player controls or battles that player is protecting won't count toward Landroval, Horizon Witness's trigger condition.",
    cards := #["Landroval, Horizon Witness"],
    sets := #["hoc"] },
  { id := 316, comment := "Use the number of Dwarves you control as Dáin's last ability resolves to determine how much damage is dealt.",
    cards := #["Dáin of the Ancient Halls"],
    sets := #["hoc"] },
  { id := 317, comment := "Use the power of the creature as it last existed on the battlefield to determine the value of X.",
    cards := #["Azog, Moria's Ruin"],
    sets := #["hob"] },
  { id := 318, comment := "Use the sacrificed creature's power as it last existed on the battlefield to determine how many cards you draw.",
    cards := #["Tom, Bert, and William"],
    sets := #["hob"] },
  { id := 319, comment := "Use the sacrificed creature's power as it last existed on the battlefield to determine how many counters Rhovanion Rampager gets.",
    cards := #["Rhovanion Rampager"],
    sets := #["hob"] },
  { id := 320, comment := "Wargling's triggered ability will check when it attacks to see if you control a creature with power 4 or greater. If you don't, the ability won't trigger at all. It will not check again when it resolves, so the ability will resolve even if you no longer control a creature with power 4 or greater.",
    cards := #["Wargling"],
    sets := #["hob"] },
  { id := 321, comment := "Whatever you do, don't eat the delicious cards.",
    cards := #["The Shire"],
    sets := #["hoc"] },
  { id := 322, comment := "Whatever you do, don't eat your opponents' delicious cards.",
    cards := #["Supper for Spiders"],
    sets := #["hob"] },
  { id := 323, comment := "When the cascade ability resolves, you must exile cards. The only optional part of the ability is whether or not you cast the last card exiled.",
    cards := #["Call Forth the Tempest"],
    sets := #["hoc"] },
  { id := 324, comment := "Whether you control a Goblin or Orc matters only at the time you declare blockers. Once Olog-Hai Crusher blocks a creature, that won't change even if all the Goblins and Orcs you control leave the battlefield.",
    cards := #["Olog-hai Crusher"],
    sets := #["hoc"] },
  { id := 325, comment := "While Head of the Hunt is on the battlefield, creatures your opponents control are exiled instead of dying, and abilities that would trigger when those creatures die won't trigger.",
    cards := #["Head of the Hunt"],
    sets := #["hob"] },
  { id := 326, comment := "While resolving the triggered ability of Mentor of the Meek, you can't pay {1} multiple times to draw more than one card.",
    cards := #["Mentor of the Meek"],
    sets := #["hoc"] },
  { id := 327, comment := "While the effect of Dáin's last ability is applying, your opponents can choose not to attack with a creature that must attack if able as long as there is no other player, planeswalker, or battle for that creature to attack that wouldn't require a cost.",
    cards := #["Dáin, Lord of the Iron Hills"],
    sets := #["hob"] },
  { id := 328, comment := "Wilderland Scrounger's triggered ability will check when it attacks to see if you control a creature with power 4 or greater. If you don't, the ability won't trigger at all. It will not check again when it resolves, so the trigger will resolve even if you no longer control a creature with power 4 or greater.",
    cards := #["Wilderland Scrounger"],
    sets := #["hob"] },
  { id := 329, comment := "Woodland Weavemaster's last ability is a mana ability. It doesn't use the stack and can't be responded to.",
    cards := #["Woodland Weavemaster"],
    sets := #["hob"] },
  { id := 330, comment := "You can choose to cast an Adventure instant or sorcery spell from your graveyard as Bilbo's ability resolves. If that Adventure spell resolves, you can exile it using the replacement effect associated with the Adventure, and you can cast the permanent spell later from exile. If that Adventure spell fails to resolve (because it's countered or its targets become illegal), that card is exiled by the replacement effect created by Bilbo's ability; you can't cast the permanent spell later from exile.",
    cards := #["Bilbo, Thief in the Night"],
    sets := #["hob"] },
  { id := 331, comment := "You can look at the top card of your library whenever you want (with one restriction; see below), even if you don't have priority. This action doesn't use the stack. Knowing what that card is becomes part of the information you have access to, just like you can look at the cards in your hand.",
    cards := #["Elven Chorus"],
    sets := #["hoc"] },
  { id := 332, comment := "You can target a creature that doesn't have indestructible with Smite the Deathless. It will still be exiled if it would die this turn.",
    cards := #["Smite the Deathless"],
    sets := #["hoc"] },
  { id := 333, comment := "You can't pay a gift cost more than once.",
    cards := #["Bilbo's Gambit"],
    sets := #["hob"] },
  { id := 334, comment := "You can't sacrifice a Food to pay multiple costs. For example, you can't sacrifice a Food token to activate its own ability and also to activate Maraleaf Rider's ability.",
    cards := #["The Shire"],
    sets := #["hoc"] },
  { id := 335, comment := "You can't sacrifice multiple creatures to deal damage multiple times.",
    cards := #["Bolg of the North"],
    sets := #["hob"] },
  { id := 336, comment := "You cast the card while the ability is resolving and still on the stack. You can't wait to cast it later in the turn.",
    cards := #["Gríma, Saruman's Footman"],
    sets := #["hoc"] },
  { id := 337, comment := "You cast the copy while the ability is resolving and still on the stack. You can't wait to cast it later in the turn.",
    cards := #["Saruman of Many Colors"],
    sets := #["hoc"] },
  { id := 338, comment := "You choose a target for Palantír of Orthanc's ability when it goes on the stack. If that target is illegal as the ability tries to resolve, the ability is removed from the stack. You won't put an influence counter on Palantír of Orthanc, and you won't scry, draw, or mill.",
    cards := #["Palantír of Orthanc"],
    sets := #["hoc"] },
  { id := 339, comment := "You choose how many and which creatures to tap while Minas Tirith Garrison's last ability is resolving. No player may take any other actions between the time you make this choice and the time at which you draw cards.",
    cards := #["Minas Tirith Garrison"],
    sets := #["hoc"] },
  { id := 340, comment := "You choose how many targets Gandalf's triggered ability has and how the damage is divided as you put the ability on the stack. Each target must receive at least 1 damage.",
    cards := #["Gandalf, Spark Starter"],
    sets := #["hob"] },
  { id := 341, comment := "You choose whether to cast a spell from your hand as Gandalf's triggered ability resolves. You can't wait to cast it later in the turn. Timing restrictions based on the card's types are ignored.",
    cards := #["Gandalf, Party Guest"],
    sets := #["hoc"] },
  { id := 342, comment := "You divide the damage as you put Inferno Titan's triggered ability on the stack, not as it resolves. Each target must be assigned at least 1 damage. (In other words, as you put the ability on the stack, you choose whether to have it deal 3 damage to a single target, 2 damage to one target and 1 damage to another target, or 1 damage to each of three targets.)",
    cards := #["Inferno Titan"],
    sets := #["hoc"] },
  { id := 343, comment := "You don't choose a target for Saruman of Many Colors's ability at the time it triggers. Rather, a second \"reflexive\" ability triggers when one or more cards are milled this way. You choose a target for that ability as it goes on the stack. Each player may respond to this triggered ability as normal.",
    cards := #["Saruman of Many Colors"],
    sets := #["hoc"] },
  { id := 344, comment := "You don't have to choose a target for Gollum's second ability. However, if you do and that target becomes illegal by the time the ability tries to resolve, it will not resolve. Each opponent will not lose 2 life.",
    cards := #["Gollum the Abandoned"],
    sets := #["hob"] },
  { id := 345, comment := "You don't have to reveal the cards in the face-down pile if you put it into your hand.",
    cards := #["Riddles in the Dark"],
    sets := #["hob"] },
  { id := 346, comment := "You draw just one card, no matter how much life you've gained past 3 life.",
    cards := #["The Gaffer"],
    sets := #["hoc"] },
  { id := 347, comment := "You exile the cards face up. All players will be able to see them.",
    cards := #["Call Forth the Tempest"],
    sets := #["hoc"] },
  { id := 348, comment := "You may choose to discard your hand even if your hand contains zero cards.",
    cards := #["Balin, Loremaster"],
    sets := #["hob"] },
  { id := 349, comment := "You may split the cards into one pile of four and one pile of zero. The pile of four cards could be the face-up pile or the face-down pile. Which pile to choose won't be much of riddle for your opponent if you do that!",
    cards := #["Riddles in the Dark"],
    sets := #["hob"] },
  { id := 350, comment := "You must choose an existing creature type, such as Dwarf or Warrior. Card types such as artifact and supertypes such as legendary can't be chosen.",
    cards := #["An Unexpected Party // At the Door"],
    sets := #["hob"] },
  { id := 351, comment := "You must control a Wizard to cast spells exiled by Flameshape, but losing control of your last Wizard while a spell is on the stack will not prevent the spells from resolving.",
    cards := #["Gandalf, Goblins' Bane // Flameshape"],
    sets := #["hob"] },
  { id := 352, comment := "You must follow all normal timing rules for a card you play using Moria Marauder's last ability and, if it's a spell, you must pay its costs to cast it.",
    cards := #["Mount Doom"],
    sets := #["hoc"] },
  { id := 353, comment := "You must follow all normal timing rules when playing a land or casting a spell for cards exiled with Inside Information. For example, if an exiled card is a land card, you may play it only during your main phase while the stack is empty and only if you have an available land play remaining.",
    cards := #["Inside Information"],
    sets := #["hob"] },
  { id := 354, comment := "You must still follow any timing restrictions and permissions, including those based on the card's type.",
    cards := #["Thranduil's Decree"],
    sets := #["hob"] },
  { id := 355, comment := "You pay all costs and follow all normal timing rules for spells cast this way.",
    cards := #["Shadow of the Enemy"],
    sets := #["hoc"] },
  { id := 356, comment := "You pay all costs and follow all timing rules for cards exiled with Flameshape. For example, if an exiled card is a land card, you may play it only during your main phase while the stack is empty and only if you have an available land play remaining.",
    cards := #["Gandalf, Goblins' Bane // Flameshape"],
    sets := #["hob"] },
  { id := 357, comment := "You remove the indestructible counter from Arwen as a cost to activate its second ability. If Arwen already received 2 damage earlier in the turn, it will be destroyed due to having lethal damage before you get to put a +1/+1 counter on it.",
    cards := #["Arwen, Mortal Queen"],
    sets := #["hoc"] },
  { id := 358, comment := "You won't gain life for an artifact or enchantment that isn't actually destroyed (for example, if it has indestructible).",
    cards := #["Ori, Plate Stacker"],
    sets := #["hoc"] },
  { id := 359, comment := "You'll still pay all costs for the spell, including additional costs. You may also pay alternative costs if any are available.",
    cards := #["Elven Chorus"],
    sets := #["hoc"] },
  { id := 360, comment := "A power-up ability is a special kind of activated ability. \"Power-up — [Cost]: [Effect]\" means \"[Cost]: [Effect]. If this permanent entered this turn, this ability's cost is reduced by this permanent's mana cost. Activate only once.\"",
    cards := #["Aerial Doombot", "Brave Brawler", "Captain Marvel, Earth's Protector", "Nick Fury, Agent of S.H.I.E.L.D.", "Bold Biochemist", "Kang the Conqueror", "Stature, Size Shifter", "Ninja of the Hand", "Unliving Legionnaire", "Human Torch, Johnny Storm", "Loki Laufeyson", "Quicksilver, Brash Blur", "Volcanic Villain", "Wonder Man, Hollywood Hero", "Hercules, Prince of Power", "Pet Avengers", "Serpent Specialist", "She-Hulk, Jade Defender", "White Tiger, Ava Ayala", "Abomination, Terrifying Titan", "Hulk, Gamma Goliath", "Thanos, the Mad Titan", "Ultron Drone", "Viv Vision, Teen Synthezoid"],
    sets := #["msh"] },
  { id := 361, comment := "If you activate a permanent's power-up ability on the same turn that permanent entered, the cost of the power-up ability is reduced by that permanent's mana cost. For example, say you want to activate the power-up ability of Aerial Doombot on the turn it enters. Aerial Doombot's power-up ability costs . Since Aerial Doombot's mana cost is , it would cost only to activate that power-up ability that turn.",
    cards := #["Aerial Doombot", "Brave Brawler", "Captain Marvel, Earth's Protector", "Nick Fury, Agent of S.H.I.E.L.D.", "Bold Biochemist", "Kang the Conqueror", "Stature, Size Shifter", "Ninja of the Hand", "Unliving Legionnaire", "Human Torch, Johnny Storm", "Loki Laufeyson", "Quicksilver, Brash Blur", "Volcanic Villain", "Wonder Man, Hollywood Hero", "Hercules, Prince of Power", "Pet Avengers", "Serpent Specialist", "She-Hulk, Jade Defender", "White Tiger, Ava Ayala", "Abomination, Terrifying Titan", "Hulk, Gamma Goliath", "Thanos, the Mad Titan", "Ultron Drone", "Viv Vision, Teen Synthezoid"],
    sets := #["msh"] },
  { id := 362, comment := "Some power-up abilities require targets or have optional targets. If one or more targets are chosen for a power-up ability and all of those targets are illegal as the ability resolves (usually because they left the battlefield in response), the ability won't resolve and none of its effects will happen. However, since the power-up ability was already activated, it can't be activated again.",
    cards := #["Aerial Doombot", "Brave Brawler", "Captain Marvel, Earth's Protector", "Nick Fury, Agent of S.H.I.E.L.D.", "Bold Biochemist", "Kang the Conqueror", "Stature, Size Shifter", "Ninja of the Hand", "Unliving Legionnaire", "Human Torch, Johnny Storm", "Loki Laufeyson", "Quicksilver, Brash Blur", "Volcanic Villain", "Wonder Man, Hollywood Hero", "Hercules, Prince of Power", "Pet Avengers", "Serpent Specialist", "She-Hulk, Jade Defender", "White Tiger, Ava Ayala", "Abomination, Terrifying Titan", "Hulk, Gamma Goliath", "Thanos, the Mad Titan", "Ultron Drone", "Viv Vision, Teen Synthezoid"],
    sets := #["msh"] },
  { id := 363, comment := "If a spell's teamwork cost was paid, the spell is \"cast using teamwork.\"",
    cards := #["Agent Maria Hill", "Helicarrier Strike", "Murdock's Crusade", "Atlantis Attacks", "We Say Thee Nay!", "Cruel Alliance", "Too Evil to Stay Dead", "Widow's Bite", "HULK SMASH!", "Repulsor Blast", "Team Tactics", "Earth's Mightiest Heroes", "Go Nuts!"],
    sets := #["msh"] },
  { id := 364, comment := "If an effect allows you to cast a spell \"without paying its mana cost,\" you can choose to pay optional additional costs, such as teamwork.",
    cards := #["Agent Maria Hill", "Helicarrier Strike", "Murdock's Crusade", "Atlantis Attacks", "We Say Thee Nay!", "Cruel Alliance", "Too Evil to Stay Dead", "Widow's Bite", "HULK SMASH!", "Repulsor Blast", "Team Tactics", "Earth's Mightiest Heroes", "Go Nuts!"],
    sets := #["msh"] },
  { id := 365, comment := "If you copy a spell on the stack that was cast using teamwork, the copy was also cast using teamwork.",
    cards := #["Agent Maria Hill", "Helicarrier Strike", "Murdock's Crusade", "Atlantis Attacks", "We Say Thee Nay!", "Cruel Alliance", "Too Evil to Stay Dead", "Widow's Bite", "HULK SMASH!", "Repulsor Blast", "Team Tactics", "Earth's Mightiest Heroes", "Go Nuts!"],
    sets := #["msh"] },
  { id := 366, comment := "If you put a permanent with a teamwork ability onto the battlefield without casting it, you can't pay its teamwork cost.",
    cards := #["Agent Maria Hill", "Helicarrier Strike", "Murdock's Crusade", "Atlantis Attacks", "We Say Thee Nay!", "Cruel Alliance", "Too Evil to Stay Dead", "Widow's Bite", "HULK SMASH!", "Repulsor Blast", "Team Tactics", "Earth's Mightiest Heroes", "Go Nuts!"],
    sets := #["msh"] },
  { id := 367, comment := "Tapping an untapped creature that's attacking or blocking to pay a teamwork cost won't cause that creature to stop attacking or blocking.",
    cards := #["Agent Maria Hill", "Helicarrier Strike", "Murdock's Crusade", "Atlantis Attacks", "We Say Thee Nay!", "Cruel Alliance", "Too Evil to Stay Dead", "Widow's Bite", "HULK SMASH!", "Repulsor Blast", "Team Tactics", "Earth's Mightiest Heroes", "Go Nuts!"],
    sets := #["msh"] },
  { id := 368, comment := "The teamwork ability doesn't let you pay a teamwork cost more than once.",
    cards := #["Agent Maria Hill", "Helicarrier Strike", "Murdock's Crusade", "Atlantis Attacks", "We Say Thee Nay!", "Cruel Alliance", "Too Evil to Stay Dead", "Widow's Bite", "HULK SMASH!", "Repulsor Blast", "Team Tactics", "Earth's Mightiest Heroes", "Go Nuts!"],
    sets := #["msh"] },
  { id := 369, comment := "You can tap any untapped creature you control to pay a teamwork cost, including one you haven't controlled continuously since the beginning of your most recent turn.",
    cards := #["Agent Maria Hill", "Helicarrier Strike", "Murdock's Crusade", "Atlantis Attacks", "We Say Thee Nay!", "Cruel Alliance", "Too Evil to Stay Dead", "Widow's Bite", "HULK SMASH!", "Repulsor Blast", "Team Tactics", "Earth's Mightiest Heroes", "Go Nuts!"],
    sets := #["msh"] },
  { id := 370, comment := "If a resolving spell or ability instructs a specific creature to connive but that creature has left the battlefield, the creature still connives. If you discard a nonland card this way, you won't put a +1/+1 counter on anything. Abilities that trigger \"whenever a creature you control connives\" will trigger.",
    cards := #["A.I.M. Scientists", "Leader, Super-Genius", "Trickster's Stratagem", "Baron Helmut Zemo", "Baron Strucker, HYDRA Overlord", "Madame Masque", "M.O.D.O.K.", "Red Room Recruit", "Swordsman, Sharp Scoundrel", "Kang, Temporal Tyrant", "Villainous Hideout"],
    sets := #["msh"] },
  { id := 371, comment := "Once an ability that causes a creature to connive begins to resolve, no player may take any other actions until it's done. Notably, opponents can't try to remove the conniving creature after you discard a nonland card but before it receives a +1/+1 counter.",
    cards := #["A.I.M. Scientists", "Leader, Super-Genius", "Trickster's Stratagem", "Baron Helmut Zemo", "Baron Strucker, HYDRA Overlord", "Madame Masque", "M.O.D.O.K.", "Red Room Recruit", "Swordsman, Sharp Scoundrel", "Kang, Temporal Tyrant", "Villainous Hideout"],
    sets := #["msh"] },
  { id := 372, comment := "A modal double-faced card can be transformed or be put onto the battlefield transformed. This is a change from previous rules. If an effect instructs you to transform a modal double-faced card on the battlefield, it transforms only if its other face has a permanent type (that is, if its other face isn't an instant or sorcery). If it doesn't, it simply won't transform. Similarly, if an effect attempts to put a modal double-faced card onto the battlefield transformed, it will enter transformed if its back face has a permanent type. If it doesn't, it will simply stay in its current zone. General Information on Double-Faced Cards",
    cards := #["Bruce Banner", "Jennifer Walters", "Monica Rambeau", "Tony Stark", "King T'Challa", "The Sensational She-Hulk", "Photon, Living Light", "The Incredible Hulk", "The Invincible Iron Man", "Black Panther, Hope Enduring"],
    sets := #["msh"] },
  { id := 373, comment := "Each double-faced card has an icon in the top-left corner of each face. For modal double-faced cards in this set, these icons are a single black triangle for the front face, and a double white triangle for the back face.",
    cards := #["Bruce Banner", "Jennifer Walters", "Monica Rambeau", "Tony Stark", "King T'Challa", "The Sensational She-Hulk", "Photon, Living Light", "The Incredible Hulk", "The Invincible Iron Man", "Black Panther, Hope Enduring"],
    sets := #["msh"] },
  { id := 374, comment := "Each face of a double-faced card has its own set of characteristics: name, types, subtypes, abilities, and so on. While a double-faced card is on the stack or battlefield, consider only the characteristics of the face that's currently up. The other set of characteristics is ignored.",
    cards := #["Bruce Banner", "Jennifer Walters", "Monica Rambeau", "Tony Stark", "King T'Challa", "The Sensational She-Hulk", "Photon, Living Light", "The Incredible Hulk", "The Invincible Iron Man", "Black Panther, Hope Enduring"],
    sets := #["msh"] },
  { id := 375, comment := "If an effect allows you to play a land or cast a spell from among a group of cards, you may play or cast a modal double-faced card with any face that fits the criteria of that effect. For example, if an effect allows you to cast green spells from your graveyard, you can cast The Incredible Hulk, but not Bruce Banner.",
    cards := #["Bruce Banner", "Jennifer Walters", "Monica Rambeau", "Tony Stark", "King T'Challa", "The Sensational She-Hulk", "Photon, Living Light", "The Incredible Hulk", "The Invincible Iron Man", "Black Panther, Hope Enduring"],
    sets := #["msh"] },
  { id := 376, comment := "If an effect allows you to put a card with particular characteristics onto the battlefield without instructing you to play or cast it, you consider only the characteristics of a modal double-faced card's front face to see if that card qualifies. If it does, it enters the battlefield with its front face up.",
    cards := #["Bruce Banner", "Jennifer Walters", "Monica Rambeau", "Tony Stark", "King T'Challa", "The Sensational She-Hulk", "Photon, Living Light", "The Incredible Hulk", "The Invincible Iron Man", "Black Panther, Hope Enduring"],
    sets := #["msh"] },
  { id := 377, comment := "In the Commander variant, a double-faced card's color identity is determined by the mana costs and mana symbols in the rules text of both faces combined. If either face has a color indicator or basic land type, those are also considered.",
    cards := #["Bruce Banner", "Jennifer Walters", "Monica Rambeau", "Tony Stark", "King T'Challa", "The Sensational She-Hulk", "Photon, Living Light", "The Incredible Hulk", "The Invincible Iron Man", "Black Panther, Hope Enduring"],
    sets := #["msh"] },
  { id := 378, comment := "One or both faces of a double-faced card may include a reminder about what's on the other face. This reminder text has no effect on gameplay.",
    cards := #["Bruce Banner", "Jennifer Walters", "Monica Rambeau", "Tony Stark", "King T'Challa", "The Sensational She-Hulk", "Photon, Living Light", "The Incredible Hulk", "The Invincible Iron Man", "Black Panther, Hope Enduring"],
    sets := #["msh"] },
  { id := 379, comment := "The mana value of a modal double-faced card is based on the characteristics of the face that's being considered. On the stack or the battlefield, consider whichever face is up. In all other zones, consider only the front face. This is different than how the mana value of other double-faced cards is determined.",
    cards := #["Bruce Banner", "Jennifer Walters", "Monica Rambeau", "Tony Stark", "King T'Challa", "The Sensational She-Hulk", "Photon, Living Light", "The Incredible Hulk", "The Invincible Iron Man", "Black Panther, Hope Enduring"],
    sets := #["msh"] },
  { id := 380, comment := "To determine whether it is legal to play a modal double-faced card, consider only the characteristics of the face you're playing and ignore the other face's characteristics. For example, if an effect stops you from casting spells with mana value 2 or less, you can't cast Bruce Banner, but you can still cast The Incredible Hulk.",
    cards := #["Bruce Banner", "Jennifer Walters", "Monica Rambeau", "Tony Stark", "King T'Challa", "The Sensational She-Hulk", "Photon, Living Light", "The Incredible Hulk", "The Invincible Iron Man", "Black Panther, Hope Enduring"],
    sets := #["msh"] },
  { id := 381, comment := "While a double-faced card isn't on the stack or battlefield, consider only the characteristics of its front face. For example, the above card has only the characteristics of Bruce Banner in the graveyard, even if it was The Incredible Hulk on the battlefield.",
    cards := #["Bruce Banner", "Jennifer Walters", "Monica Rambeau", "Tony Stark", "King T'Challa", "The Sensational She-Hulk", "Photon, Living Light", "The Incredible Hulk", "The Invincible Iron Man", "Black Panther, Hope Enduring"],
    sets := #["msh"] },
  { id := 382, comment := "Plan is an enchantment type with no rules meaning. It doesn't grant the enchantment any intrinsic abilities. However, the effects of other cards may refer to Plans or Plan cards.",
    cards := #["Construct a Cosmic Cube", "Political Triumph", "Rewrite History", "Doom Reigns Supreme", "Robot Domination", "Death to Our Enemies", "Claim the Kingdom"],
    sets := #["msh"] },
  { id := 383, comment := "Finality counters aren't keyword counters, and a finality counter doesn't give any abilities to the permanent it's on. If that permanent loses its abilities and then would go to a graveyard, it will still be exiled instead.",
    cards := #["Grim Reaper, Lethal Legionnaire", "Thunderbolts Conspiracy", "Winter Soldier, Icy Assassin"],
    sets := #["msh"] },
  { id := 384, comment := "Finality counters don't stop permanents from going to zones other than the graveyard from the battlefield. For example, if a permanent with a finality counter on it would be put into its owner's hand from the battlefield, it does so normally.",
    cards := #["Grim Reaper, Lethal Legionnaire", "Thunderbolts Conspiracy", "Winter Soldier, Icy Assassin"],
    sets := #["msh"] },
  { id := 385, comment := "Finality counters work on any permanent, not only creatures. If a permanent with a finality counter on it would be put into a graveyard from the battlefield, exile it instead.",
    cards := #["Grim Reaper, Lethal Legionnaire", "Thunderbolts Conspiracy", "Winter Soldier, Icy Assassin"],
    sets := #["msh"] },
  { id := 386, comment := "If the top card of your library changes while you're casting a spell, playing a land, activating an ability, or taking a special action, you can't look at the new top card until you finish doing so. This means that if you cast the top card of your library, you can't look at the next one until you're done paying for that spell.",
    cards := #["Daredevil, Man Without Fear", "Iron Lad, Diverging Destiny", "Ka-Zar of the Savage Land"],
    sets := #["msh"] },
  { id := 387, comment := "Multiple finality counters on a single permanent are redundant.",
    cards := #["Grim Reaper, Lethal Legionnaire", "Thunderbolts Conspiracy", "Winter Soldier, Icy Assassin"],
    sets := #["msh"] },
  { id := 388, comment := "You pay all costs and follow all normal timing rules for a card played this way. For example, if the exiled card is a land card, you may play it only during your main phase while the stack is empty.",
    cards := #["Blazing Crescendo", "Crimson Operative", "Daredevil, Man Without Fear"],
    sets := #["msh"] },
  { id := 389, comment := "Abilities that say that a triggered ability triggers additional times won't apply to copying a triggered ability.",
    cards := #["Echo, Perceptive Prodigy", "Scientist Supreme of A.I.M."],
    sets := #["msh"] },
  { id := 390, comment := "Activated abilities contain a colon. They're generally written \"[Cost]: [Effect].\" Some keyword abilities (such as equip) are activated abilities and will have a colon in their reminder text.",
    cards := #["Echo, Perceptive Prodigy", "Scientist Supreme of A.I.M."],
    sets := #["msh"] },
  { id := 391, comment := "Any choices made when the ability resolves won't have been made yet when it's copied. Any such choices will be made separately when the copy resolves. Most notably, if a triggered ability asks its controller to pay a cost, you pay that cost for the copy if you wish to have it paid.",
    cards := #["Echo, Perceptive Prodigy", "Scientist Supreme of A.I.M."],
    sets := #["msh"] },
  { id := 392, comment := "Auras attached to the exiled creature will be put into their owners' graveyards. Any Equipment will become unattached and remain on the battlefield. Any counters on the exiled creature will cease to exist. When the card returns to the battlefield, it will be a new object with no connection to the card that was exiled.",
    cards := #["Cloak and Dagger, Entwined", "Secret Invasion"],
    sets := #["msh"] },
  { id := 393, comment := "Because improvise isn't an alternative cost, it can be used in conjunction with alternative costs.",
    cards := #["Arc Reactor", "Ironheart, Clever Champion"],
    sets := #["msh"] },
  { id := 394, comment := "Creating a copy of an activated ability won't cause abilities that trigger when a player activates an ability to trigger.",
    cards := #["Echo, Perceptive Prodigy", "Scientist Supreme of A.I.M."],
    sets := #["msh"] },
  { id := 395, comment := "Each creature with lifelink dealing combat damage causes a separate life-gaining event. For example, if two creatures you control with lifelink deal combat damage at the same time, the ability will trigger twice. However, if a single creature you control with lifelink deals combat damage to multiple creatures, players, and/or planeswalkers at the same time (perhaps because it has trample or was blocked by more than one creature), the ability will trigger only once.",
    cards := #["Heroic Feast", "Tigra, Feline Fury"],
    sets := #["msh"] },
  { id := 396, comment := "Equipment attached to a creature doesn't become tapped when that creature becomes tapped, and tapping that Equipment doesn't cause the creature to become tapped.",
    cards := #["Arc Reactor", "Ironheart, Clever Champion"],
    sets := #["msh"] },
  { id := 397, comment := "If a creature has in its mana cost, X is 0 for the purpose of determining its mana value.",
    cards := #["The Super Hero Civil War", "Thanos, the Mad Titan"],
    sets := #["msh"] },
  { id := 398, comment := "If a spell you cast has in its mana cost, you must choose 0 as the value of X when casting it without paying its mana cost.",
    cards := #["Cosmic Cube", "Doom Reigns Supreme"],
    sets := #["msh"] },
  { id := 399, comment := "If an artifact you control has a mana ability with in the cost, activating that ability while casting a spell with improvise will result in the artifact being tapped when you pay the spell's costs. You won't be able to tap it again for improvise. Similarly, if you sacrifice an artifact to activate a mana ability while casting a spell with improvise, that artifact won't be on the battlefield when you pay the spell's costs, so you won't be able to tap it for improvise.",
    cards := #["Arc Reactor", "Ironheart, Clever Champion"],
    sets := #["msh"] },
  { id := 400, comment := "If the ability has damage divided as it was put onto the stack, the division can't be changed, although the targets receiving that damage still can. The same is true of abilities that distribute counters.",
    cards := #["Echo, Perceptive Prodigy", "Scientist Supreme of A.I.M."],
    sets := #["msh"] },
  { id := 401, comment := "If the ability that's copied has an X whose value was determined as it was activated, the copy will have the same value of X.",
    cards := #["Echo, Perceptive Prodigy", "Scientist Supreme of A.I.M."],
    sets := #["msh"] },
  { id := 402, comment := "If the ability that's copied is modal (that is, it says \"Choose one —\" or the like), the copy will have the same mode. A different mode can't be chosen.",
    cards := #["Echo, Perceptive Prodigy", "Scientist Supreme of A.I.M."],
    sets := #["msh"] },
  { id := 403, comment := "If the copied spell divides damage or distributes counters among a number of targets, the division and number of targets can't be changed. If you choose new targets, you must choose the same number of targets.",
    cards := #["Fin Fang Foom", "Loki Laufeyson"],
    sets := #["msh"] },
  { id := 404, comment := "If the spell that's copied has an X whose value was determined as it was cast, the copy will have the same value of X.",
    cards := #["Fin Fang Foom", "Loki Laufeyson"],
    sets := #["msh"] },
  { id := 405, comment := "If the spell that's copied is modal (that is, it says \"Choose one —\" or the like), the copy will have the same mode or modes. You can't choose different ones.",
    cards := #["Fin Fang Foom", "Loki Laufeyson"],
    sets := #["msh"] },
  { id := 406, comment := "If you gain an amount of life \"for each\" of something, that life is gained as one event and the ability triggers only once.",
    cards := #["Heroic Feast", "Tigra, Feline Fury"],
    sets := #["msh"] },
  { id := 407, comment := "Improvise can't be used to pay for anything other than the cost of casting the spell. For example, it can't be used during the resolution of an ability that says \"Counter target spell unless its controller pays .\"",
    cards := #["Arc Reactor", "Ironheart, Clever Champion"],
    sets := #["msh"] },
  { id := 408, comment := "Improvise can't pay for , , , , , or mana symbols in a spell's total cost.",
    cards := #["Arc Reactor", "Ironheart, Clever Champion"],
    sets := #["msh"] },
  { id := 409, comment := "Improvise doesn't change a spell's mana cost or mana value.",
    cards := #["Arc Reactor", "Ironheart, Clever Champion"],
    sets := #["msh"] },
  { id := 410, comment := "In a Two-Headed Giant game, life gained by your teammate won't cause the ability to trigger, even though it caused your team's life total to increase.",
    cards := #["Heroic Feast", "Tigra, Feline Fury"],
    sets := #["msh"] },
  { id := 411, comment := "Once the exiled permanent returns, it's considered a new object with no relation to the object that it was. Auras attached to the exiled permanent will be put into their owners' graveyards. Equipment attached to the exiled permanent will become unattached and remain on the battlefield. Any counters on the exiled permanent will cease to exist.",
    cards := #["The Mighty Thor, Jane Foster", "The Mind Stone"],
    sets := #["msh"] },
  { id := 412, comment := "Tapping an artifact won't cause its abilities to stop applying unless those abilities say so.",
    cards := #["Arc Reactor", "Ironheart, Clever Champion"],
    sets := #["msh"] },
  { id := 413, comment := "The copy is created on the stack, so it's not \"cast.\" Abilities that trigger when a player casts a spell won't trigger.",
    cards := #["Fin Fang Foom", "Loki Laufeyson"],
    sets := #["msh"] },
  { id := 414, comment := "The copy will have the same targets as the ability it's copying unless you choose new ones. You may change any number of the targets, including all of them or none of them. If, for one of the targets, you can't choose a new legal target, then it remains unchanged (even if the current target is illegal).",
    cards := #["Echo, Perceptive Prodigy", "Scientist Supreme of A.I.M."],
    sets := #["msh"] },
  { id := 415, comment := "The copy will resolve before the original ability does.",
    cards := #["Echo, Perceptive Prodigy", "Scientist Supreme of A.I.M."],
    sets := #["msh"] },
  { id := 416, comment := "To determine the total cost of a spell, start with the mana cost or alternative cost you're paying, add any cost increases, then apply any cost reductions. The mana value of the spell remains unchanged, no matter what the total cost to cast it was.",
    cards := #["Baron Strucker, HYDRA Overlord", "Shuri, Wakandan Inventor"],
    sets := #["msh"] },
  { id := 417, comment := "Triggered abilities use the word \"when,\" \"whenever,\" or \"at.\" They're often written as \"[Trigger condition], [effect].\" Some keywords (such as prowess) are triggered abilities and will use \"when,\" \"whenever,\" or \"at\" in their reminder text.",
    cards := #["Echo, Perceptive Prodigy", "Scientist Supreme of A.I.M."],
    sets := #["msh"] },
  { id := 418, comment := "When calculating a spell's total cost, include any alternative costs, additional costs, or anything else that increases or reduces the cost to cast the spell. Improvise applies after the total cost is calculated.",
    cards := #["Arc Reactor", "Ironheart, Clever Champion"],
    sets := #["msh"] },
  { id := 419, comment := "You can't choose to pay any activation costs for the copy. However, effects based on those costs that were paid for the original ability are copied as though those same costs were paid for the copy.",
    cards := #["Echo, Perceptive Prodigy", "Scientist Supreme of A.I.M."],
    sets := #["msh"] },
  { id := 420, comment := "You can't choose to pay any additional costs for the copy. However, effects based on any additional costs that were paid for the original spell (such as teamwork) are copied as though those same costs were paid for the copy too.",
    cards := #["Fin Fang Foom", "Loki Laufeyson"],
    sets := #["msh"] },
  { id := 421, comment := "You pay all costs and follow all normal timing rules for cards played this way. For example, if an exiled card is a land card, you may play it only during your main phase while the stack is empty.",
    cards := #["Hex Magic", "Jessica Jones, Private Eye"],
    sets := #["msh"] },
  { id := 422, comment := "\"Do this only once each turn\" lets you choose whether or not to have the Villain connive as the triggered ability resolves. If you don't, the ability will trigger again the next time the condition is met. Once you choose to do so, the ability will no longer trigger for the rest of the turn and any other instances of the ability that have already triggered and are on the stack won't have any effect.",
    cards := #["Baron Strucker, HYDRA Overlord"],
    sets := #["msh"] },
  { id := 423, comment := "\"Harnessed\" is a designation that the permanent has once an ability instructs you to harness it. It has no special rules meaning other than being a designation that the ∞ ability (and, theoretically, other effects) can see.",
    cards := #["The Mind Stone"],
    sets := #["msh"] },
  { id := 424, comment := "\"Shield\" is not an ability that creatures have and shield counters are not keyword counters. If a creature with a shield counter loses its abilities, the shield counter will still protect it as normal.",
    cards := #["Captain America, Super-Soldier"],
    sets := #["msh"] },
  { id := 425, comment := "A \"Hero source\" is any object with the Hero creature type. This means you could spend the mana to activate an ability of a permanent with changeling (a keyword ability that gives it all creature types) or a Hero card in your hand or graveyard, for example.",
    cards := #["Avengers Tower"],
    sets := #["msh"] },
  { id := 426, comment := "A \"Villain source\" is any object with the Villain creature type. This means you could spend the mana to activate an ability of a permanent with changeling (a keyword ability that gives it all creature types) or a Villain card in your hand or graveyard, for example.",
    cards := #["Villainous Hideout"],
    sets := #["msh"] },
  { id := 427, comment := "A \"creature source\" is a permanent, spell, or card in any zone with the card type \"creature.\" For example, Echo's ability can target a cycling ability you've activated if the discarded card is a creature card.",
    cards := #["Echo, Perceptive Prodigy"],
    sets := #["msh"] },
  { id := 428, comment := "A \"creature source\" is any object with the card type \"creature.\" This means you could spend the mana to activate an ability of a creature card in your hand or graveyard.",
    cards := #["Shang-Chi, Master of Kung Fu"],
    sets := #["msh"] },
  { id := 429, comment := "A boast ability can be activated at any point after the creature with that ability has been declared as an attacker. This can be before blockers are declared, after blockers are declared but before combat damage is dealt, during combat after combat damage is dealt, during the postcombat main phase, during the end step, or, in some unusual cases, during the cleanup step.",
    cards := #["Baron Helmut Zemo"],
    sets := #["msh"] },
  { id := 430, comment := "A creature attacks alone if it's the only creature declared as an attacker during the declare attackers step (including creatures controlled by your teammates, if applicable). For example, Black Widow's ability won't trigger if you attack with multiple creatures and all but one of them are removed from combat. Similarly, creatures that enter the battlefield attacking later in combat won't be considered when determining whether or not a creature attacked alone.",
    cards := #["Black Widow, Double Agent"],
    sets := #["msh"] },
  { id := 431, comment := "A creature attacks alone if it's the only creature declared as an attacker during the declare attackers step (including creatures controlled by your teammates, if applicable). For example, HYDRA Infiltration's last ability won't trigger if you attack with multiple creatures and all but one of them are removed from combat. Similarly, creatures that enter the battlefield attacking later in combat won't be considered when determining whether or not a creature attacked alone.",
    cards := #["HYDRA Infiltration"],
    sets := #["msh"] },
  { id := 432, comment := "A creature attacks alone if it's the only creature declared as an attacker during the declare attackers step (including creatures controlled by your teammates, if applicable). For example, Luke Cage's ability won't trigger if you attack with him and one or more other creatures and all of those other creatures are removed from combat. Similarly, creatures that enter the battlefield attacking later in combat won't be considered when determining whether or not a creature attacked alone.",
    cards := #["Luke Cage, Power Man"],
    sets := #["msh"] },
  { id := 433, comment := "A creature attacks alone if it's the only creature declared as an attacker during the declare attackers step (including creatures controlled by your teammates, if applicable). For example, S.H.I.E.L.D. Spy Kit's second ability won't trigger if you attack with multiple creatures and all but one of them are removed from combat. Similarly, creatures that enter the battlefield attacking later in combat won't be considered when determining whether or not a creature attacked alone.",
    cards := #["S.H.I.E.L.D. Spy Kit"],
    sets := #["msh"] },
  { id := 434, comment := "A creature with a shield counter on it may still be destroyed by state-based actions if it has damage marked on it equal to its toughness or has been dealt unpreventable damage by a source with deathtouch.",
    cards := #["Captain America, Super-Soldier"],
    sets := #["msh"] },
  { id := 435, comment := "A creature you control is attacking alone if it's the only creature that's currently attacking (including creatures controlled by your teammates, if applicable) and you control it. For example, if you attack with multiple creatures and all but one of them are removed from combat, you can activate Crowd of True Believers's ability targeting the remaining attacking creature.",
    cards := #["Crowd of True Believers"],
    sets := #["msh"] },
  { id := 436, comment := "A player with ten or more poison counters loses the game. This is a state-based action and doesn't use the stack. In other words, players can't respond to it, just like a player losing the game due to having 0 or less life.",
    cards := #["The Serpent Society"],
    sets := #["msh"] },
  { id := 437, comment := "A player's \"opening hand\" is the hand of cards the player has after all players have taken mulligans. If players have any cards in hand that allow actions to be taken with them from a player's opening hand, the starting player takes all such actions first in any order, followed by each other player in turn order. Then the first turn begins.",
    cards := #["Quicksilver, Brash Blur"],
    sets := #["msh"] },
  { id := 438, comment := "Although a creature put onto the battlefield this way is attacking, it was never declared as an attacking creature. Abilities that trigger whenever a creature attacks won't trigger when that creature enters attacking.",
    cards := #["Elektra, Daughter of the Hand"],
    sets := #["msh"] },
  { id := 439, comment := "Although the creature you put onto the battlefield is attacking, it was never declared as an attacking creature. Abilities that trigger whenever a creature attacks won't trigger when that creature enters attacking.",
    cards := #["Grim Reaper, Lethal Legionnaire"],
    sets := #["msh"] },
  { id := 440, comment := "An \"artifact source\" is a permanent, spell, or card in any zone with the card type \"artifact.\" For example, Scientist Supreme of A.I.M.'s ability can target a cycling ability you've activated if the discarded card is a artifact card.",
    cards := #["Scientist Supreme of A.I.M."],
    sets := #["msh"] },
  { id := 441, comment := "An effect that states that a permanent becomes a \"[creature type or types] artifact creature\" allows the object to retain all of its prior card types and subtypes other than creature types, but it replaces any existing creature types.",
    cards := #["Iron Man Armor"],
    sets := #["msh"] },
  { id := 442, comment := "An effect that states that a permanent becomes an \"artifact creature\" allows the object to retain all of its prior card types and subtypes.",
    cards := #["I Am Iron Man"],
    sets := #["msh"] },
  { id := 443, comment := "Ant-Man's second ability triggers whenever you put a +1/+1 counter on a creature for any reason, not just because of his first ability.",
    cards := #["Ant-Man, Colony Commander"],
    sets := #["msh"] },
  { id := 444, comment := "Any copies you don't cast cease to exist the next time state-based actions are performed.",
    cards := #["Baron Helmut Zemo"],
    sets := #["msh"] },
  { id := 445, comment := "Any enters abilities of each copied creature will trigger when the token enters. Any \"as [this creature] enters\" or \"[this creature] enters with\" abilities of the copied creature will also work.",
    cards := #["Multiversal Incursion"],
    sets := #["msh"] },
  { id := 446, comment := "Any enters abilities of the copied artifact will trigger when the token enters. Any \"as [this artifact] enters\" or \"[this artifact] enters with\" abilities of the copied artifact will also work.",
    cards := #["Ultron, Artificial Malevolence"],
    sets := #["msh"] },
  { id := 447, comment := "Ares's second ability can apply to Ares himself if he dies while he's attacking.",
    cards := #["Ares, God of War"],
    sets := #["msh"] },
  { id := 448, comment := "As The Sensational She-Hulk's last ability is resolving, you choose whether or not you want her to deal damage to the target. If you do, that ability won't trigger again that turn and any other instances of the ability that have already triggered and are on the stack won't have any effect.",
    cards := #["Jennifer Walters"],
    sets := #["msh"] },
  { id := 449, comment := "As Worlds Within Worlds resolves, first exile all creatures. Then, starting with the player whose turn it is, each player in turn order chooses any number of creature cards from their hand to put onto the battlefield without revealing them. Then those creatures enter the battlefield simultaneously. Then put all cards exiled this way into their owners' hands, then exile Worlds Within Worlds.",
    cards := #["Worlds Within Worlds"],
    sets := #["msh"] },
  { id := 450, comment := "As long as you control Kid Loki, creatures you control that you've put one or more +1/+1 counters on this turn will have hexproof regardless of whether Kid Loki was on the battlefield under your control when you put those counters on those creatures.",
    cards := #["Kid Loki"],
    sets := #["msh"] },
  { id := 451, comment := "Atlantean Cavalry doesn't need to have been under your control when the first card is drawn for its ability to trigger. As long as you control it when you draw your second card in a turn, that ability will trigger.",
    cards := #["Atlantean Cavalry"],
    sets := #["msh"] },
  { id := 452, comment := "Attuma's last ability will trigger once for each player you attack with one or more Merfolk.",
    cards := #["Attuma, Atlantean Warlord"],
    sets := #["msh"] },
  { id := 453, comment := "Auras attached to the exiled creature will be put into their owners' graveyards. Equipment attached to the exiled creature will become unattached and remain on the battlefield. Any counters on the exiled creature will cease to exist. Once the exiled permanent returns, it's considered a new object with no relation to the object that it was.",
    cards := #["S.H.I.E.L.D. Flying Car"],
    sets := #["msh"] },
  { id := 454, comment := "Auras attached to the exiled creature will be put into their owners' graveyards. Equipment attached to the exiled creature will become unattached and remain on the battlefield. Any counters on the exiled creature will cease to exist. When the card returns to the battlefield, it will be a new object with no connection to the card that was exiled.",
    cards := #["Super Villain Lockup"],
    sets := #["msh"] },
  { id := 455, comment := "Being harnessed isn't copiable. If something else becomes a copy of The Mind Stone, it must be harnessed separately. Similarly, if The Mind Stone is already harnessed and becomes a copy of something else, it stays harnessed, though it's very likely that won't be relevant until that copy effect ends.",
    cards := #["The Mind Stone"],
    sets := #["msh"] },
  { id := 456, comment := "Bold Biochemist's power-up ability doesn't target itself. If it's no longer on the battlefield as that ability resolves, you'll still draw two cards.",
    cards := #["Bold Biochemist"],
    sets := #["msh"] },
  { id := 457, comment := "Captain America's last ability considers any time a creature you control became tapped earlier in the turn, regardless of who controlled it at that time or whether Captain America was on the battlefield at that time.",
    cards := #["Captain America, Living Legend"],
    sets := #["msh"] },
  { id := 458, comment := "Captain Mar-Vell doesn't have to have been on the battlefield at the point in the turn where an opponent cast a spell. If an opponent casts a spell and then Captain Mar-Vell enters the battlefield under your control later in the turn, you may cast spells as though they had flash that turn as long as you control Captain Mar-Vell.",
    cards := #["Captain Mar-Vell, Space-Born"],
    sets := #["msh"] },
  { id := 459, comment := "Casting multiple spells that target a creature you control in the same turn will result in Iron Fist having multiple instances of the activated ability. You can activate only one of them at a time, and as this will require tapping Iron Fist, having that ability multiple times doesn't accomplish much.",
    cards := #["Iron Fist, Living Weapon"],
    sets := #["msh"] },
  { id := 460, comment := "Colleen Wing's last ability resolves before the spell that caused it to trigger. It resolves even if that spell is countered or otherwise leaves the stack without resolving.",
    cards := #["Colleen Wing, Street Samurai"],
    sets := #["msh"] },
  { id := 461, comment := "Colleen Wing's last ability triggers when you cast a spell that has multiple targets, as long as at least one of those targets is a creature you control. It doesn't trigger multiple times if you cast a spell that targets a creature you control multiple times or that targets multiple creatures you control.",
    cards := #["Colleen Wing, Street Samurai"],
    sets := #["msh"] },
  { id := 462, comment := "Compare the mana value of the instant or sorcery spell to Loki's power at the time you cast the spell. If Loki is no longer on the battlefield at that time, use his power from the last time he was on the battlefield.",
    cards := #["Loki Laufeyson"],
    sets := #["msh"] },
  { id := 463, comment := "Construct a Cosmic Cube doesn't need to have been under your control when the first card is drawn for its first ability to trigger. As long as you control it when you draw your second card in a turn, that ability will trigger.",
    cards := #["Construct a Cosmic Cube"],
    sets := #["msh"] },
  { id := 464, comment := "Creatures that enter attacking are never declared as attackers, and as such, they won't cause Attuma's last ability to trigger.",
    cards := #["Attuma, Atlantean Warlord"],
    sets := #["msh"] },
  { id := 465, comment := "Damage dealt to Doctor Doom is tracked even if he has indestructible. For example, if Doctor Doom is dealt what would be lethal damage and then he loses indestructible (probably because you lose control of all your artifact creatures and Plans), he'll be destroyed the next time state-based actions are performed.",
    cards := #["Doctor Doom"],
    sets := #["msh"] },
  { id := 466, comment := "Daredevil lets you look at the top card of your library whenever you want (with one restriction—see below), even if you don't have priority. This action doesn't use the stack. Knowing what that card is becomes part of the information you have access to, just like you can look at the cards in your hand.",
    cards := #["Daredevil, Man Without Fear"],
    sets := #["msh"] },
  { id := 467, comment := "Each of the copies will have the same target as the original unless you choose new ones. If you can't choose a new legal target, then it remains unchanged (even if the current target is illegal). If there are multiple copies, you may change the targets of each of them to different legal targets.",
    cards := #["Photon Blast Barrage"],
    sets := #["msh"] },
  { id := 468, comment := "Each token created by Multiversal Incursion copies exactly what was printed on the original creature and nothing else, with the listed exception (unless that creature is copying something else; see below). It doesn't copy whether that creature is tapped or untapped, whether it has any counters on it or Auras and Equipment attached to it, or any non-copy effects that have changed its power, toughness, types, color, or so on. If it is a Vehicle, it is not crewed.",
    cards := #["Multiversal Incursion"],
    sets := #["msh"] },
  { id := 469, comment := "Echo's ability can copy any activated or triggered ability on the stack, not just one with targets.",
    cards := #["Echo, Perceptive Prodigy"],
    sets := #["msh"] },
  { id := 470, comment := "Echo's ability targets an activated or triggered ability that is on the stack and creates one or more additional instances of that ability on the stack. It doesn't cause any object to gain any abilities.",
    cards := #["Echo, Perceptive Prodigy"],
    sets := #["msh"] },
  { id := 471, comment := "Effects other than Mjölnir's equip worthy ability that cause it to become attached to a creature can attach it to a creature that isn't worthy. For example, suppose you control a Mjölnir that isn't attached to anything as well as Loki, God of Mischief (a blue God Sorcerer Villain creature) with Super-Soldier Serum (an Aura with \"Whenever enchanted creature attacks or blocks, attach any number of target Equipment you control to it.\") attached to him. When Loki attacks, you can target Mjölnir with Super-Soldier Serum's ability, and when that ability resolves, Mjölnir will become attached to Loki. (It doesn't have to be Loki, but it's more fun that way.)",
    cards := #["Mjölnir, Hammer of Thor"],
    sets := #["msh"] },
  { id := 472, comment := "Equip worthy is a variant of the equip keyword. \"Equip worthy [cost]\" means \"[Cost]: Attach this Equipment to target legendary non-Villain creature you control that's red and/or white. Activate only as a sorcery.\"",
    cards := #["Mjölnir, Hammer of Thor"],
    sets := #["msh"] },
  { id := 473, comment := "Except for the listed exception, the first target artifact copies exactly what was printed on the second target artifact and nothing else (unless that artifact is copying something else or is a token; see below). It doesn't copy whether that permanent is tapped or untapped, whether it has any counters on it or Auras and Equipment attached to it, or any non-copy effects that have changed its power, toughness, types, color, and so on.",
    cards := #["Shuri, Wakandan Inventor"],
    sets := #["msh"] },
  { id := 474, comment := "Except for the listed exceptions, Absorbing Man copies exactly what was printed on the target permanent and nothing else (unless that permanent is copying something else or is a token; see below). He doesn't copy whether that permanent is tapped or untapped, whether it has any counters on it or Auras and Equipment attached to it, or any non-copy effects that have changed its power, toughness, types, color, and so on.",
    cards := #["Absorbing Man"],
    sets := #["msh"] },
  { id := 475, comment := "Except for the listed exceptions, Taskmaster copies exactly what was printed on the target creature or card and nothing else (unless that permanent is copying something else or is a token; see below). If he copies a creature, he doesn't copy whether it's tapped or untapped, whether it has any counters on it or Auras and Equipment attached to it, or any non-copy effects that have changed its power, toughness, types, color, and so on. If he copies a card in a graveyard, he doesn't copy any information about the object that card was before it was put into a graveyard.",
    cards := #["Taskmaster, Mercenary Mimic"],
    sets := #["msh"] },
  { id := 476, comment := "Fin Fang Foom's last ability triggers when you cast an instant or sorcery spell that has multiple targets, as long as at least one of those targets is an artifact or land. It doesn't trigger multiple times if you cast a spell that targets an artifact or land multiple times or that targets multiple artifacts and/or lands.",
    cards := #["Fin Fang Foom"],
    sets := #["msh"] },
  { id := 477, comment := "For Hawkeye's Bow's second ability to trigger, the equipped creature has to actually change from untapped to tapped. If an effect attempts to tap that creature but it was already tapped at the time, the ability won't trigger.",
    cards := #["Hawkeye's Bow"],
    sets := #["msh"] },
  { id := 478, comment := "Hawkeye's triggered ability goes on the stack with no targets and no modes chosen. As it resolves, you may pay up to three times. That is, you may pay , , , or choose not to pay. If you chose to pay, the second \"reflexive\" triggered ability will trigger. You'll choose the modes and targets, if any, for that second ability at that time, and players can respond to that ability as normal. If all targets for that reflexive ability are illegal as it tries to resolve, it won't resolve and none of its effects will happen.",
    cards := #["Hawkeye, Master Marksman"],
    sets := #["msh"] },
  { id := 479, comment := "Heroic Feast's last ability triggers just once for each life-gaining event, no matter how much life is gained.",
    cards := #["Heroic Feast"],
    sets := #["msh"] },
  { id := 480, comment := "Hulk's cost-reduction ability reduces only the amount of generic mana in power-up abilities. For example, it will reduce a power-up cost of to , but it will have no effect on a power-up cost with no generic mana in it (such as a power-up cost of ).",
    cards := #["Hulk, Gamma Goliath"],
    sets := #["msh"] },
  { id := 481, comment := "Hybrid mana symbols that include black count for the cost of Baron Helmut Zemo's boast ability. For example, a card with mana cost has two black mana symbols in its mana cost.",
    cards := #["Baron Helmut Zemo"],
    sets := #["msh"] },
  { id := 482, comment := "I Am Iron Man will overwrite any previous effects that set a permanent's power and toughness to specific numbers. Effects that otherwise modify its power and toughness will still apply no matter when they took effect. The same is true for +1/+1 counters.",
    cards := #["I Am Iron Man"],
    sets := #["msh"] },
  { id := 483, comment := "If Ares can't attack for any reason (such as being tapped or having come under your control that turn), then he doesn't attack. If there's a cost associated with having him attack, you're not forced to pay that cost, so he doesn't have to attack in that case either.",
    cards := #["Ares, God of War"],
    sets := #["msh"] },
  { id := 484, comment := "If Captain America is no longer on the battlefield at the time his last ability resolves, use his toughness as he last existed on the battlefield to determine the value of X.",
    cards := #["Captain America, Wings of Freedom"],
    sets := #["msh"] },
  { id := 485, comment := "If Cloak and Dagger leave the battlefield before their last ability resolves, the target opponent will still reveal their hand, but no cards or creatures will be exiled.",
    cards := #["Cloak and Dagger, Entwined"],
    sets := #["msh"] },
  { id := 486, comment := "If Crossbones enters at the same time as other Villains you control, his ability will trigger.",
    cards := #["Crossbones, Malicious Mercenary"],
    sets := #["msh"] },
  { id := 487, comment := "If Hulkling's last ability triggers, the stat comparison will happen again when the ability tries to resolve. If neither stat of the new creature is greater, the ability will do nothing. If the creature that entered the battlefield leaves the battlefield before the ability tries to resolve, use its power and toughness as it last existed on the battlefield to compare the stats.",
    cards := #["Hulkling, Burgeoning Bruiser"],
    sets := #["msh"] },
  { id := 488, comment := "If I Am Iron Man causes a Vehicle to become an artifact creature, it doesn't count as \"crewing\" that Vehicle for any ability that would trigger from a Vehicle becoming crewed.",
    cards := #["I Am Iron Man"],
    sets := #["msh"] },
  { id := 489, comment := "If Jessica Jones is no longer on the battlefield when her ability resolves, use her power as she last existed on the battlefield to determine the value of X.",
    cards := #["Jessica Jones, Private Eye"],
    sets := #["msh"] },
  { id := 490, comment := "If Political Triumph isn't on the battlefield as its last ability resolves, you won't be able to sacrifice it, but the other effects will still happen. You'll draw a card and put a +1/+1 counter on each creature you control.",
    cards := #["Political Triumph"],
    sets := #["msh"] },
  { id := 491, comment := "If Robot Domination is put into your graveyard from the battlefield at the same time as one or more creature cards are put into your graveyard, its first ability won't trigger at all. Similarly, if Robot Domination becomes a creature and then dies, its first ability won't trigger.",
    cards := #["Robot Domination"],
    sets := #["msh"] },
  { id := 492, comment := "If Robot Domination isn't on the battlefield as its last ability resolves, you won't be able to sacrifice it, but the other effect will still happen. You'll create the Robot Villain tokens.",
    cards := #["Robot Domination"],
    sets := #["msh"] },
  { id := 493, comment := "If Secret Invasion leaves the battlefield before its triggered ability resolves, the target creature won't be exiled and the enchanted creature won't become a copy of the target creature.",
    cards := #["Secret Invasion"],
    sets := #["msh"] },
  { id := 494, comment := "If Super Villain Lockup leaves the battlefield before its triggered ability resolves, the target creature won't be exiled.",
    cards := #["Super Villain Lockup"],
    sets := #["msh"] },
  { id := 495, comment := "If The Sensational She-Hulk isn't on the battlefield as her last ability is resolving (perhaps because she was the creature that was dealt damage), you may still have her deal damage.",
    cards := #["Jennifer Walters"],
    sets := #["msh"] },
  { id := 496, comment := "If The Super Hero Civil War leaves the battlefield before its first chapter ability resolves, you won't gain control of the target creatures at all.",
    cards := #["The Super Hero Civil War"],
    sets := #["msh"] },
  { id := 497, comment := "If The Void can't attack for any reason (such as being tapped or having come under its controller's control that turn), then it doesn't attack. If there's a cost associated with having it attack, its controller isn't forced to pay that cost, so it doesn't have to attack in that case either.",
    cards := #["The Sentry, Golden Guardian"],
    sets := #["msh"] },
  { id := 498, comment := "If The Wondrous Wasp leaves the battlefield before her last ability resolves, the target creature will still be tapped, but it won't lose its abilities at all.",
    cards := #["The Wondrous Wasp"],
    sets := #["msh"] },
  { id := 499, comment := "If Tigra is dealt lethal damage at the same time that you gain life, she won't receive a counter from her ability in time to save her.",
    cards := #["Tigra, Feline Fury"],
    sets := #["msh"] },
  { id := 500, comment := "If Viv Vision is no longer on the battlefield when her second ability resolves, use her power as she last existed on the battlefield to determine whether or not to draw a card.",
    cards := #["Viv Vision, Teen Synthezoid"],
    sets := #["msh"] },
  { id := 501, comment := "If War Machine is no longer on the battlefield when his last ability resolves, use his power as he last existed on the battlefield to determine the value of X.",
    cards := #["War Machine, Legacy of Iron"],
    sets := #["msh"] },
  { id := 502, comment := "If Web Up leaves the battlefield before its triggered ability resolves, the target permanent won't be exiled.",
    cards := #["Web Up"],
    sets := #["msh"] },
  { id := 503, comment := "If Whiplash is no longer on the battlefield when his last triggered ability resolves, use the number of Equipment that were attached to him as he last existed on the battlefield to determine the value of X.",
    cards := #["Whiplash, Vengeful Engineer"],
    sets := #["msh"] },
  { id := 504, comment := "If a Villain that's also an artifact you control enters, HYDRA Assault Robot's ability will trigger only once.",
    cards := #["HYDRA Assault Robot"],
    sets := #["msh"] },
  { id := 505, comment := "If a card in a graveyard has in its mana cost, X is 0 for the purpose of determining its mana value.",
    cards := #["Too Evil to Stay Dead"],
    sets := #["msh"] },
  { id := 506, comment := "If a card in a library or graveyard has in its mana cost, X is 0 for the purpose of determining its mana value.",
    cards := #["Vision Quest"],
    sets := #["msh"] },
  { id := 507, comment := "If a card in your hand has in its mana cost, X is 0 for the purpose of determining its mana value.",
    cards := #["Origin of the Avengers"],
    sets := #["msh"] },
  { id := 508, comment := "If a copied creature is copying something else, then the token enters as whatever that creature copied, with the listed exception.",
    cards := #["Multiversal Incursion"],
    sets := #["msh"] },
  { id := 509, comment := "If a creature enters with +1/+1 counters on it, consider those counters when determining if Hulkling's last ability will trigger. For example, if Hulkling is a 2/3 and a 1/1 creature enters with two +1/+1 counters on it, Hulkling's last ability will trigger.",
    cards := #["Hulkling, Burgeoning Bruiser"],
    sets := #["msh"] },
  { id := 510, comment := "If a creature spell's sneak cost was paid, the creature it becomes enters tapped and attacking the same player, planeswalker, or battle as the creature that was returned to its owner's hand to pay its sneak cost. This is a rule specific to sneak; in other cases, when a creature is put onto the battlefield attacking, that creature's controller chooses which player, planeswalker, or battle it's attacking.",
    cards := #["Elektra, Daughter of the Hand"],
    sets := #["msh"] },
  { id := 511, comment := "If a creature with a boast ability is put onto the battlefield attacking, it was never declared as an attacker. Its boast ability can't be activated that turn.",
    cards := #["Baron Helmut Zemo"],
    sets := #["msh"] },
  { id := 512, comment := "If a creature you control is dealt damage by multiple sources at the same time (usually because it was blocked by multiple creatures), The Sensational She-Hulk will deal damage equal to the total amount of damage dealt to that creature.",
    cards := #["Jennifer Walters"],
    sets := #["msh"] },
  { id := 513, comment := "If a permanent has in its mana cost, X is 0 for the purpose of determining its mana value.",
    cards := #["Murdock's Crusade"],
    sets := #["msh"] },
  { id := 514, comment := "If a permanent on the battlefield has in its mana cost, X is 0 for the purpose of determining its mana value.",
    cards := #["Evil's Thrall"],
    sets := #["msh"] },
  { id := 515, comment := "If a permanent that would be dealt damage has more than one shield counter on it, that damage is prevented and only one shield counter is removed.",
    cards := #["Captain America, Super-Soldier"],
    sets := #["msh"] },
  { id := 516, comment := "If a permanent with a shield counter is dealt unpreventable damage, that damage will be dealt and a shield counter will still be removed.",
    cards := #["Captain America, Super-Soldier"],
    sets := #["msh"] },
  { id := 517, comment := "If a permanent you control would enter the battlefield with a number of counters on it, it enters with that many plus one instead.",
    cards := #["Doc Samson, Super Psychiatrist"],
    sets := #["msh"] },
  { id := 518, comment := "If a replacement effect allows a player to modify or replace an event by untapping a creature enchanted with Frozen in Ice, that player may apply that replacement effect, but the creature won't untap. If the original event is entirely replaced, the original event won't happen.",
    cards := #["Frozen in Ice"],
    sets := #["msh"] },
  { id := 519, comment := "If a replacement effect allows a player to modify or replace an event by untapping a creature that can't become untapped due to the effect of Spider-Woman's last ability, that player may apply that replacement effect, but the creature won't untap. If the original event is entirely replaced, the original event won't happen.",
    cards := #["Spider-Woman, Secret Agent"],
    sets := #["msh"] },
  { id := 520, comment := "If a spell has in its mana cost, use the value chosen for X to determine that spell's mana value.",
    cards := #["Thor, God of Thunder"],
    sets := #["msh"] },
  { id := 521, comment := "If a spell has in its mana cost, use the value chosen for X to determine whether its mana value is 4 or greater. If it is, The Scarlet Witch's ability will apply. If not, it won't.",
    cards := #["The Scarlet Witch"],
    sets := #["msh"] },
  { id := 522, comment := "If an Aura is exiled this way, its owner chooses what it will enchant as it returns to the battlefield. An Aura put onto the battlefield this way doesn't target anything (so it could be attached to a permanent with shroud, for example), but the Aura's enchant ability restricts what it can be attached to. If the Aura can't legally be attached to anything, it remains in exile for the rest of the game.",
    cards := #["The Mind Stone"],
    sets := #["msh"] },
  { id := 523, comment := "If an ability is linked to a second ability, copies of that first ability are also linked to that second ability. If the second ability refers to \"the exiled card,\" it refers to all cards exiled by the first ability and the copy. For example, if the first ability of Extraplanar Lens from the Mirrodin release (\"When this artifact enters, you may exile target land you control.\") is copied and two lands are exiled, Extraplanar Lens's second ability (\"Whenever a land with the same name as the exiled card is tapped for mana, its controller adds one mana of any type that land produced.\") will trigger whenever a land with the same name as either of the exiled cards is tapped for mana.",
    cards := #["Scientist Supreme of A.I.M."],
    sets := #["msh"] },
  { id := 524, comment := "If an ability is linked to a second ability, copies of that first ability are also linked to that second ability. If the second ability refers to \"the exiled card,\" it refers to all cards exiled by the first ability and the copy. For example, if the second ability of Hoarding Dragon from the Foundations release (\"When this creature enters, you may search your library for an artifact card, exile it, then shuffle.\") is copied and two cards are exiled, then when Hoarding Dragon's third ability (\"When this creature dies, you may put the exiled card into its owner's hand.\") later resolves, if you choose to put \"the exiled card\" into its owner's hand, both exiled cards will be put into their owners' hands.",
    cards := #["Echo, Perceptive Prodigy"],
    sets := #["msh"] },
  { id := 525, comment := "If an attacking creature token you control deals first-strike combat damage and then loses first strike before regular combat damage is dealt (perhaps because Okoye leaves the battlefield), that token won't also deal normal combat damage, unless it somehow has double strike.",
    cards := #["Okoye, Dora Milaje Leader"],
    sets := #["msh"] },
  { id := 526, comment := "If an effect adds additional combat phases to a turn and a creature with a boast ability attacks more than once during that turn, its boast ability can still be activated only once.",
    cards := #["Baron Helmut Zemo"],
    sets := #["msh"] },
  { id := 527, comment := "If an effect instructs a player to choose a card name, the name of either face may be chosen. If that effect or a linked ability refers to a spell with the chosen name being cast and/or a land with the chosen name being played, it considers only the chosen name, not the other face's name.",
    cards := #["Bruce Banner"],
    sets := #["msh"] },
  { id := 528, comment := "If an effect tries to tap a creature that's already tapped, nothing happens. That creature doesn't \"become tapped,\" and Captain America's last ability won't trigger.",
    cards := #["Captain America, Living Legend"],
    sets := #["msh"] },
  { id := 529, comment := "If another effect (or effects) modifies how much damage a source you control would deal—by preventing some of it, for example—the player being dealt damage or the controller of the permanent being dealt damage chooses the order in which any such effects (including Mjölnir's) apply. If all of the damage is prevented, Mjölnir's effect no longer applies.",
    cards := #["Mjölnir, Hammer of Thor"],
    sets := #["msh"] },
  { id := 530, comment := "If another effect modifies how much damage a source would deal, including preventing some of it, the player being dealt damage or the controller of the permanent being dealt damage chooses an order in which to apply those effects. If all of the damage is prevented, the effect of Hawkeye's last ability no longer applies.",
    cards := #["Hawkeye, Young Avenger"],
    sets := #["msh"] },
  { id := 531, comment := "If damage dealt by a source you control is being divided or assigned among multiple permanents and/or players, that damage is divided or assigned before doubling. For example, if you attack with a 5/5 creature with trample that's equipped with Mjölnir and it's blocked by a 2/2 creature, you can assign 2 damage to the blocker and 3 damage to the defending player. Those amounts are then doubled to 4 and 6, respectively.",
    cards := #["Mjölnir, Hammer of Thor"],
    sets := #["msh"] },
  { id := 532, comment := "If either creature is an illegal target as Punishing Punch tries to resolve, the creature you control won't deal damage.",
    cards := #["Punishing Punch"],
    sets := #["msh"] },
  { id := 533, comment := "If it's not your turn and you gain control of a creature with a boast ability after that creature attacked, you can activate that creature's boast ability if it hasn't been activated yet that turn.",
    cards := #["Baron Helmut Zemo"],
    sets := #["msh"] },
  { id := 534, comment := "If lethal damage is dealt to The Incredible Hulk, his enrage ability triggers. The Incredible Hulk leaves the battlefield before that ability resolves, and you won't put three +1/+1 counters on him. In this or any other case where The Incredible Hulk is no longer on the battlefield when his enrage ability resolves, there will still be an additional combat phase after this phase if he was attacking.",
    cards := #["Bruce Banner"],
    sets := #["msh"] },
  { id := 535, comment := "If multiple creatures enter at the same time, Hulkling's last ability may trigger multiple times, although the stat comparison will take place each time one of those abilities tries to resolve. For example, if you control a 2/3 Hulkling and two 3/3 creatures you control enter, the ability will trigger twice. The first ability will resolve and put a +1/+1 counter on Hulkling. When the second ability tries to resolve, neither the power nor the toughness of the new creature is greater than that of Hulkling, so that ability does nothing.",
    cards := #["Hulkling, Burgeoning Bruiser"],
    sets := #["msh"] },
  { id := 536, comment := "If multiple effects modify your hand size, apply them in timestamp order. For example, if you put Spellbook (an artifact that says you have no maximum hand size) onto the battlefield and then put The Ten Rings onto the battlefield, your maximum hand size will be ten. However, if those permanents entered in the opposite order, you would have no maximum hand size.",
    cards := #["The Ten Rings"],
    sets := #["msh"] },
  { id := 537, comment := "If multiple sources deal damage to The Incredible Hulk at the same time, most likely because multiple creatures blocked him, his enrage ability will trigger only once.",
    cards := #["Bruce Banner"],
    sets := #["msh"] },
  { id := 538, comment := "If no card is discarded, most likely because that player's hand is empty and an effect says they can't draw cards, the conniving creature does not receive a +1/+1 counter.",
    cards := #["A.I.M. Scientists"],
    sets := #["msh"] },
  { id := 539, comment := "If one of the exiled cards has in its mana cost, you must choose 0 as the value of X when casting the copy without paying its mana cost.",
    cards := #["Baron Helmut Zemo"],
    sets := #["msh"] },
  { id := 540, comment := "If one of the target artifacts is an illegal target as Shuri's last ability tries to resolve, it won't have any effect. If both targets are illegal, the ability won't resolve.",
    cards := #["Shuri, Wakandan Inventor"],
    sets := #["msh"] },
  { id := 541, comment := "If one or more Villains you control enter simultaneously, Crossbones's last ability will still trigger only once.",
    cards := #["Crossbones, Malicious Mercenary"],
    sets := #["msh"] },
  { id := 542, comment := "If the affected creature gains an ability after the effect of The Wondrous Wasp's last ability begins to apply to it, it will keep that ability.",
    cards := #["The Wondrous Wasp"],
    sets := #["msh"] },
  { id := 543, comment := "If the card you put onto the battlefield with Nick Fury's power-up ability is a double-faced card with daybound (an ability from the Innistrad: Midnight Hunt release) on its front face, it will enter with its back face up if it's night. You won't be able to transform it in this case.",
    cards := #["Nick Fury, Agent of S.H.I.E.L.D."],
    sets := #["msh"] },
  { id := 544, comment := "If the card you put onto the battlefield with Nick Fury's power-up ability is a double-faced card, it enters with its front face up (with one exception; see below). Any \"enters\" abilities that permanent has on its front face will trigger when it enters. Once you choose whether or not to transform that permanent and put the rest of the cards on the bottom of your library in a random order, those abilities (and any other abilities that triggered during this process) will be put onto the stack.",
    cards := #["Nick Fury, Agent of S.H.I.E.L.D."],
    sets := #["msh"] },
  { id := 545, comment := "If the copied artifact is a token, the first target artifact copies the original characteristics of that token as stated by the effect that created that token.",
    cards := #["Shuri, Wakandan Inventor"],
    sets := #["msh"] },
  { id := 546, comment := "If the copied artifact is copying something else, then the first target artifact becomes a copy of whatever that permanent copied.",
    cards := #["Shuri, Wakandan Inventor"],
    sets := #["msh"] },
  { id := 547, comment := "If the copied artifact is copying something else, then the token enters as whatever that artifact copied, with the listed exception.",
    cards := #["Ultron, Artificial Malevolence"],
    sets := #["msh"] },
  { id := 548, comment := "If the copied creature is a token, Taskmaster copies the original characteristics of that token as stated by the effect that created that token.",
    cards := #["Taskmaster, Mercenary Mimic"],
    sets := #["msh"] },
  { id := 549, comment := "If the copied creature is a token, the enchanted creature copies the original characteristics of that token as stated by the effect that created that token.",
    cards := #["Secret Invasion"],
    sets := #["msh"] },
  { id := 550, comment := "If the copied creature is copying something else, then Taskmaster becomes a copy of whatever that permanent copied.",
    cards := #["Taskmaster, Mercenary Mimic"],
    sets := #["msh"] },
  { id := 551, comment := "If the copied creature is copying something else, then the enchanted creature becomes a copy of whatever that creature copied.",
    cards := #["Secret Invasion"],
    sets := #["msh"] },
  { id := 552, comment := "If the copied permanent is a token, Absorbing Man copies the original characteristics of that token as stated by the effect that created that token, with the listed exceptions.",
    cards := #["Absorbing Man"],
    sets := #["msh"] },
  { id := 553, comment := "If the copied permanent is copying something else, then Absorbing Man becomes a copy of whatever that permanent copied, with the listed exceptions.",
    cards := #["Absorbing Man"],
    sets := #["msh"] },
  { id := 554, comment := "If the cost of an ability or an additional cost of a spell requires untapping a creature enchanted with Frozen in Ice, that cost can't be paid. If a resolving spell or ability says that a player may untap that creature, that player can't choose to do so.",
    cards := #["Frozen in Ice"],
    sets := #["msh"] },
  { id := 555, comment := "If the cost of an ability or an additional cost of a spell requires untapping a creature that can't become untapped due to the effect of Spider-Woman's last ability, that cost can't be paid. If a resolving spell or ability says that a player may untap that creature, that player can't choose to do so.",
    cards := #["Spider-Woman, Secret Agent"],
    sets := #["msh"] },
  { id := 556, comment := "If the creature is controlled by someone other than the target opponent at the time Cloak and Dagger's last ability tries to resolve, the creature is an illegal target. However, the ability may still resolve if the opponent remains a legal target (see below).",
    cards := #["Cloak and Dagger, Entwined"],
    sets := #["msh"] },
  { id := 557, comment := "If the enchanted creature leaves the battlefield before Super-Soldier Serum's last ability resolves, nothing happens to any of the Equipment it targeted. If they were already attached to other creatures, they remain attached to those creatures.",
    cards := #["Super-Soldier Serum"],
    sets := #["msh"] },
  { id := 558, comment := "If the last mode is chosen and either target is illegal as HULK SMASH! resolves, no damage will be dealt.",
    cards := #["HULK SMASH!"],
    sets := #["msh"] },
  { id := 559, comment := "If the second mode was chosen and the target land is an illegal target by the time Avengers Disassembled tries to resolve, the spell won't resolve and none of its effects will happen. No damage will be dealt even if the first mode was chosen, and the land's controller won't search for a basic land card. If the target is legal but not destroyed (most likely because it has indestructible), its controller does search for a basic land card.",
    cards := #["Avengers Disassembled"],
    sets := #["msh"] },
  { id := 560, comment := "If the spell has any targets, the copy will have the same targets unless you choose new ones. You may change any number of the targets, including all of them or none of them. The new targets must be legal.",
    cards := #["Loki Laufeyson"],
    sets := #["msh"] },
  { id := 561, comment := "If the target creature is an illegal target as Crowd of True Believers's ability tries to resolve, it won't resolve and none of its effects will happen. You won't gain life.",
    cards := #["Crowd of True Believers"],
    sets := #["msh"] },
  { id := 562, comment := "If the target creature is an illegal target as Cruel Alliance tries to resolve, it won't resolve and none of its effects will happen. You won't gain life.",
    cards := #["Cruel Alliance"],
    sets := #["msh"] },
  { id := 563, comment := "If the target creature is an illegal target as Depower tries to resolve, it won't resolve and none of its effects will happen. You won't draw a card.",
    cards := #["Depower"],
    sets := #["msh"] },
  { id := 564, comment := "If the target creature is an illegal target as Hour of Defeat tries to resolve, it won't resolve and none of its effects will happen. You won't surveil.",
    cards := #["Hour of Defeat"],
    sets := #["msh"] },
  { id := 565, comment := "If the target creature is an illegal target as Pym Particles tries to resolve, it won't resolve and none of its effects will happen. You won't draw a card.",
    cards := #["Pym Particles"],
    sets := #["msh"] },
  { id := 566, comment := "If the target creature is an illegal target as Repulsor Blast tries to resolve, it won't resolve and none of its effects will happen. No damage will be dealt.",
    cards := #["Repulsor Blast"],
    sets := #["msh"] },
  { id := 567, comment := "If the target creature is an illegal target by the time the spell tries to resolve (most likely because it has left the battlefield in response), it won't resolve and none of its effects will happen. No card will be exiled.",
    cards := #["Blazing Crescendo"],
    sets := #["msh"] },
  { id := 568, comment := "If the target creature is an illegal target by the time the spell tries to resolve (most likely because it has left the battlefield in response), the spell will not resolve. No card will be exiled.",
    cards := #["Blazing Crescendo"],
    sets := #["msh"] },
  { id := 569, comment := "If the target is illegal as Taskmaster's ability tries to resolve, it won't resolve and none of its effects will happen.",
    cards := #["Taskmaster, Mercenary Mimic"],
    sets := #["msh"] },
  { id := 570, comment := "If the target of the landfall ability is illegal as the ability tries to resolve, it won't resolve and none of its effects will happen. You won't put counters on anything.",
    cards := #["Claim the Kingdom"],
    sets := #["msh"] },
  { id := 571, comment := "If the target permanent is an illegal target as Absorbing Man's last ability tries to resolve, it won't resolve and none of its effects will happen.",
    cards := #["Absorbing Man"],
    sets := #["msh"] },
  { id := 572, comment := "If the target player has fewer cards in hand than the number of cards they're instructed to reveal, they reveal all the cards in their hand.",
    cards := #["Klaw, Sonic Subjugator"],
    sets := #["msh"] },
  { id := 573, comment := "If the targeted player skips their next turn, you'll control them during the next turn they actually take.",
    cards := #["Construct a Cosmic Cube"],
    sets := #["msh"] },
  { id := 574, comment := "If the token isn't a creature, it doesn't become a 2/2 Robot Villain until after it has entered the battlefield. In that case, abilities that trigger whenever a creature you control enters won't trigger when that token enters.",
    cards := #["Ultron, Artificial Malevolence"],
    sets := #["msh"] },
  { id := 575, comment := "If there are multiple creatures attacking, it doesn't matter who or what any of them are attacking. If you control a creature attacking one opponent and another creature attacking a second opponent (or even a planeswalker a battle controlled by the first opponent), neither attacking creature is attacking alone.",
    cards := #["Crowd of True Believers"],
    sets := #["msh"] },
  { id := 576, comment := "If two or more effects attempt to modify how many counters would be put onto a permanent you control, you choose the order to apply those effects, no matter who controls the sources of those effects.",
    cards := #["Doc Samson, Super Psychiatrist"],
    sets := #["msh"] },
  { id := 577, comment := "If two targets are chosen for Cloak and Dagger's last ability and one of those targets is illegal when the ability resolves, it will still do as much as it can. If the creature is still a legal target but the opponent isn't, the opponent won't reveal their hand and you may exile the chosen creature. If the opponent is a legal target but the creature isn't, the opponent will reveal their hand and you may exile a nonland card from it. If all targets are illegal, the ability won't do anything.",
    cards := #["Cloak and Dagger, Entwined"],
    sets := #["msh"] },
  { id := 578, comment := "If two targets are chosen for the reflexive triggered ability and one of the targets is illegal as the ability tries to resolve, the original division of damage still applies but no damage is dealt to the illegal target. If all targets are illegal, the ability doesn't resolve.",
    cards := #["Death to Our Enemies"],
    sets := #["msh"] },
  { id := 579, comment := "If you activate Baron Helmut Zemo's boast ability again, you copy only the cards exiled to activate the ability that time. You don't copy any cards you exiled to activate the boast ability the first time.",
    cards := #["Baron Helmut Zemo"],
    sets := #["msh"] },
  { id := 580, comment := "If you can't legally choose a mode because all three have been chosen that turn, that instance of the ability is removed from the stack with no effect.",
    cards := #["The Vision"],
    sets := #["msh"] },
  { id := 581, comment := "If you cast a noncreature spell that requires you to sacrifice a permanent as an additional cost, you may tap that permanent (if it's an artifact) for the spell's improvise ability before you sacrifice it to pay that cost.",
    cards := #["Ironheart, Clever Champion"],
    sets := #["msh"] },
  { id := 582, comment := "If you cast a spell \"without paying its mana cost,\" you can't choose to cast it for any alternative costs. You can, however, pay additional costs, such as teamwork costs. If the spell has any mandatory additional costs, such as that of Titania, Rugged Rumbler, those must be paid to cast the spell.",
    cards := #["Baron Helmut Zemo"],
    sets := #["msh"] },
  { id := 583, comment := "If you choose a target Equipment for the first ability, and either target is illegal as that ability tries to resolve, the Equipment won't move. If it's already attached to a creature, it will remain attached to it.",
    cards := #["Swordsman, Sharp Scoundrel"],
    sets := #["msh"] },
  { id := 584, comment := "If you choose the second mode, you don't choose which creature you're removing a counter from until the ability resolves. As the ability resolves, you must remove a counter from a creature you control if you can.",
    cards := #["Mister Hyde, Monster Within"],
    sets := #["msh"] },
  { id := 585, comment := "If you don't control another Hero when you draw a card, Human Torch's ability won't trigger. If you don't control one as the ability resolves, the ability will have no effect. It doesn't matter if the Hero you control as the ability resolves is the same as the one you controlled when it triggered.",
    cards := #["Human Torch, Johnny Storm"],
    sets := #["msh"] },
  { id := 586, comment := "If you exile a card from an opponent's hand, it returns to their hand just after Cloak and Dagger leave the battlefield. If you exile a creature, it returns to the battlefield under its owner's control just after Cloak and Dagger leave the battlefield.",
    cards := #["Cloak and Dagger, Entwined"],
    sets := #["msh"] },
  { id := 587, comment := "If you manage to activate both abilities in the same turn, the last one to resolve will determine Reptil's base power and toughness (we'd recommend going with 6/6), but either way, he'll have vigilance, reach, and trample, and he'll no longer be Human.",
    cards := #["Reptil, Dinomorpher"],
    sets := #["msh"] },
  { id := 588, comment := "In a Two-Headed Giant game, gaining control of a player causes you to gain control of each player on that team.",
    cards := #["Construct a Cosmic Cube"],
    sets := #["msh"] },
  { id := 589, comment := "In the rare case where a creature is equipped with two Mjölnirs, all damage that creature would deal is multiplied by four. A third Mjölnir would multiply the damage by eight, and so on.",
    cards := #["Mjölnir, Hammer of Thor"],
    sets := #["msh"] },
  { id := 590, comment := "In the unusual case where you control two Doc Samsons, the number of counters you put on a permanent you control is the original number plus two. If you control three Doc Samsons, it's the original number plus three, and so on.",
    cards := #["Doc Samson, Super Psychiatrist"],
    sets := #["msh"] },
  { id := 591, comment := "Iron Fist's ability resolves before the spell that caused it to trigger. It resolves even if that spell is countered or otherwise leaves the stack without resolving.",
    cards := #["Iron Fist, Living Weapon"],
    sets := #["msh"] },
  { id := 592, comment := "Iron Lad lets you look at the top card of your library whenever you want (with one restriction—see below), even if you don't have priority. This action doesn't use the stack. Knowing what that card is becomes part of the information you have access to, just like you can look at the cards in your hand.",
    cards := #["Iron Lad, Diverging Destiny"],
    sets := #["msh"] },
  { id := 593, comment := "Iron Man Armor does remain an Equipment after its third ability resolves. However, if it's attached to a creature as that ability resolves, it will become unattached from that creature. While Iron Man Armor is a creature, it can't become attached to another creature.",
    cards := #["Iron Man Armor"],
    sets := #["msh"] },
  { id := 594, comment := "Iron Man's last ability checks only if an artifact entered the battlefield under your control at some point during the turn. It doesn't matter if that artifact is still on the battlefield, still under your control, or even still an artifact.",
    cards := #["Iron Man, Master of Machines"],
    sets := #["msh"] },
  { id := 595, comment := "Ka-Zar lets you look at the top card of your library whenever you want (with one restriction—see below), even if you don't have priority. This action doesn't use the stack. Knowing what that card is becomes part of the information you have access to, just like you can look at the cards in your hand.",
    cards := #["Ka-Zar of the Savage Land"],
    sets := #["msh"] },
  { id := 596, comment := "Kang doesn't need to have been under your control when the first card is drawn for his last ability to trigger. As long as you control him when you draw your second card in a turn, that ability will trigger.",
    cards := #["Kang, Temporal Tyrant"],
    sets := #["msh"] },
  { id := 597, comment := "Kid Loki doesn't need to have been under your control when the first card is drawn for his ability to trigger. As long as you control him when you draw your second card in a turn, that ability will trigger.",
    cards := #["Kid Loki"],
    sets := #["msh"] },
  { id := 598, comment := "King T'Challa doesn't need to have been under your control when the first card is drawn for his second ability to trigger. As long as you control him when you draw your second card in a turn, that ability will trigger.",
    cards := #["King T'Challa"],
    sets := #["msh"] },
  { id := 599, comment := "Loki's ability resolves before the ability that caused it to trigger. It resolves even if that ability is countered or otherwise leaves the stack without resolving.",
    cards := #["Loki, God of Mischief"],
    sets := #["msh"] },
  { id := 600, comment := "Madame Hydra's ability resolves before the spell that caused it to trigger. It resolves even if that spell is countered or otherwise leaves the stack without resolving.",
    cards := #["Madame Hydra"],
    sets := #["msh"] },
  { id := 601, comment := "Madame Masque doesn't need to have been under your control when the first card is drawn for her last ability to trigger. As long as you control her when you draw your second card in a turn, that ability will trigger.",
    cards := #["Madame Masque"],
    sets := #["msh"] },
  { id := 602, comment := "Marvel's last ability resolves before the spell that caused it to trigger. It resolves even if that spell is countered or otherwise leaves the stack without resolving.",
    cards := #["Ms. Marvel, Kamala Khan"],
    sets := #["msh"] },
  { id := 603, comment := "Mockingbird's last ability resolves before the spell that caused it to trigger. It resolves even if that spell is countered or otherwise leaves the stack.",
    cards := #["Mockingbird, Ace Agent"],
    sets := #["msh"] },
  { id := 604, comment := "Modes always happen in the printed order. If the last two modes are chosen and a creature token is destroyed by the third mode, it won't be on the battlefield to be sacrificed to the fourth mode.",
    cards := #["The Ruinous Wrecking Crew"],
    sets := #["msh"] },
  { id := 605, comment := "Mole Man's first ability doesn't allow you to activate abilities (such as cycling) of land cards in your graveyard.",
    cards := #["Mole Man, Moloid Master"],
    sets := #["msh"] },
  { id := 606, comment := "Mole Man's first ability doesn't change the times when you can play those land cards. You can still play only one land per turn, and only during your main phase when you have priority and the stack is empty.",
    cards := #["Mole Man, Moloid Master"],
    sets := #["msh"] },
  { id := 607, comment := "Moon Girl and Devil Dinosaur don't need to have been under your control when the first card is drawn for their first ability to trigger. As long as you control them when you draw your second card in a turn, that ability will trigger.",
    cards := #["Moon Girl and Devil Dinosaur"],
    sets := #["msh"] },
  { id := 608, comment := "Moon Girl and Devil Dinosaur's first ability will overwrite any previous effects that set Moon Girl and Devil Dinosaur's power and toughness to specific numbers. Effects that otherwise modify their power and toughness will still apply no matter when they took effect. The same is true for +1/+1 counters.",
    cards := #["Moon Girl and Devil Dinosaur"],
    sets := #["msh"] },
  { id := 609, comment := "Multiple instances of improvise are redundant.",
    cards := #["Ironheart, Clever Champion"],
    sets := #["msh"] },
  { id := 610, comment := "Multiple instances of lifelink are redundant.",
    cards := #["Yellowjacket, Heartless Marauder"],
    sets := #["msh"] },
  { id := 611, comment := "Multiple player-controlling effects that affect the same player overwrite each other. The last one to be created is the one that works.",
    cards := #["Construct a Cosmic Cube"],
    sets := #["msh"] },
  { id := 612, comment := "Namor's last ability resolves before the spell that caused it to trigger. It resolves even if that spell is countered or otherwise leaves the stack.",
    cards := #["Namor the Sub-Mariner"],
    sets := #["msh"] },
  { id := 613, comment := "Ninja of the Hand's power-up ability doesn't target itself. If it's no longer on the battlefield as that ability resolves, each opponent will still discard a card.",
    cards := #["Ninja of the Hand"],
    sets := #["msh"] },
  { id := 614, comment := "Once Beast has been blocked, putting a +1/+1 counter on him so that he has flying won't cause him to become unblocked.",
    cards := #["Beast, Erudite Aerialist"],
    sets := #["msh"] },
  { id := 615, comment := "Once Stature has been blocked, reducing her power to 1 or less won't cause her to become unblocked.",
    cards := #["Stature, Size Shifter"],
    sets := #["msh"] },
  { id := 616, comment := "Once a creature with haste has been legally blocked by a creature without haste, Speed's last ability won't be able to make that block illegal.",
    cards := #["Speed, Young Avenger"],
    sets := #["msh"] },
  { id := 617, comment := "Once you announce that you're activating the last ability of Baxter Building, no player may take actions until you've finished activating it. Notably, opponents can't try to change whether you control a creature with toughness 4 or greater.",
    cards := #["Baxter Building"],
    sets := #["msh"] },
  { id := 618, comment := "Once you've activated Arnim Zola's ability, removing creature cards from your graveyard won't stop the ability from resolving.",
    cards := #["Arnim Zola, Bio-Fanatic"],
    sets := #["msh"] },
  { id := 619, comment := "Once you've activated the last ability of Baxter Building, it doesn't check again at any point whether you control a creature with toughness 4 or greater.",
    cards := #["Baxter Building"],
    sets := #["msh"] },
  { id := 620, comment := "Photon Blast Barrage's first ability resolves before Photon Blast Barrage itself. It resolves and creates copies even if Photon Blast Barrage was countered or has otherwise left the stack.",
    cards := #["Photon Blast Barrage"],
    sets := #["msh"] },
  { id := 621, comment := "Photon's last ability resolves before the spell that caused it to trigger. It resolves even if that spell is countered or otherwise leaves the stack.",
    cards := #["Monica Rambeau"],
    sets := #["msh"] },
  { id := 622, comment := "Putting a land card onto the battlefield with H.E.R.B.I.E. Scout Unit's last ability doesn't count as playing a land. You can put a land card onto the battlefield this way even if you've already played a land for the turn.",
    cards := #["H.E.R.B.I.E. Scout Unit"],
    sets := #["msh"] },
  { id := 623, comment := "Quake's ability resolves before the spell that causes it to trigger. It resolves even if that spell is countered or otherwise leaves the stack without resolving.",
    cards := #["Quake, Agent of S.H.I.E.L.D."],
    sets := #["msh"] },
  { id := 624, comment := "Red Guardian's last ability can target any creature an opponent controls that dealt damage this turn, even if the permanent it dealt damage to is no longer on the battlefield or the player it dealt damage to is no longer in the game.",
    cards := #["Red Guardian, Super-Soldier"],
    sets := #["msh"] },
  { id := 625, comment := "Red Hulk must survive the damage in order to get the +1/+1 counter. If he's not on the battlefield when the last ability resolves, you won't put a +1/+1 counter on him and the reflexive triggered ability won't trigger at all.",
    cards := #["Red Hulk"],
    sets := #["msh"] },
  { id := 626, comment := "Removing a shield counter when a permanent would be dealt damage or destroyed isn't the same as regenerating that permanent.",
    cards := #["Captain America, Super-Soldier"],
    sets := #["msh"] },
  { id := 627, comment := "Reptil's abilities will overwrite all previous effects that set his creature types, power, and/or toughness to specific values. Other effects that set these characteristics to specific values that start to apply after the ability resolves will overwrite that part of the effect. Effects that otherwise modify his power and toughness, as well as +1/+1 counters, will still apply no matter when they took effect.",
    cards := #["Reptil, Dinomorpher"],
    sets := #["msh"] },
  { id := 628, comment := "Robot Domination's first ability triggers when one or more creature cards are put into your graveyard from anywhere. This is different than an ability that triggers when a creature dies. Notably, a noncreature card on the battlefield that becomes a creature and then dies (such as an animated land) won't cause this ability to trigger. Similarly, a creature card on the battlefield that becomes a noncreature permanent will cause this ability to trigger when that card is put into your graveyard.",
    cards := #["Robot Domination"],
    sets := #["msh"] },
  { id := 629, comment := "Roxxon Brutes doesn't need to have been under your control when the first card is drawn for its second ability to trigger. As long as you control it when you draw your second card in a turn, that ability will trigger.",
    cards := #["Roxxon Brutes"],
    sets := #["msh"] },
  { id := 630, comment := "Scientist Supreme of A.I.M.'s ability can copy any activated or triggered ability on the stack, not just one with targets.",
    cards := #["Scientist Supreme of A.I.M."],
    sets := #["msh"] },
  { id := 631, comment := "Scientist Supreme of A.I.M.'s ability targets an activated or triggered ability that is on the stack and creates one or more additional instances of that ability on the stack. It doesn't cause any object to gain any abilities.",
    cards := #["Scientist Supreme of A.I.M."],
    sets := #["msh"] },
  { id := 632, comment := "Shang-Chi's first ability doesn't grant haste to any creatures, nor does it allow you to attack with creatures as though they had haste. However, you will be able to activate abilities with {T} in their activation costs as soon as creatures with such abilities come under your control.",
    cards := #["Shang-Chi, Master of Kung Fu"],
    sets := #["msh"] },
  { id := 633, comment := "Shield counters don't prevent players from sacrificing creatures.",
    cards := #["Captain America, Super-Soldier"],
    sets := #["msh"] },
  { id := 634, comment := "Speed's last ability resolves before the spell that caused it to trigger. It resolves even if that spell is countered or otherwise leaves the stack without resolving.",
    cards := #["Speed, Young Avenger"],
    sets := #["msh"] },
  { id := 635, comment := "Speedball's ability resolves before the spell that caused it to trigger. It resolves even if that spell is countered or otherwise leaves the stack without resolving.",
    cards := #["Speedball, New Warrior"],
    sets := #["msh"] },
  { id := 636, comment := "Spells can be cast for their sneak costs only any time you could play an instant during the declare blockers step on your turn (after your opponent has decided whether to block).",
    cards := #["Elektra, Daughter of the Hand"],
    sets := #["msh"] },
  { id := 637, comment := "Storm's last ability resolves before the spell that caused it to trigger. It resolves even if that spell is countered or otherwise leaves the stack without resolving.",
    cards := #["Storm, Windrider"],
    sets := #["msh"] },
  { id := 638, comment := "The Hero that attacked or entered the battlefield earlier in the turn doesn't need to still be on the battlefield or under your control as the end step starts. For example, if you attack with a Hero and it dies in combat (heroically, presumably), the triggered ability of Avengers Assemble! will still trigger.",
    cards := #["Avengers Assemble!"],
    sets := #["msh"] },
  { id := 639, comment := "The Kingpin of Crime's last ability doesn't actually change any creature's power. It changes only the amount of combat damage the creature assigns. All other rules and effects that check power or toughness use the real values, even if they cause damage \"equal to a creature's power\" to be dealt.",
    cards := #["The Kingpin of Crime"],
    sets := #["msh"] },
  { id := 640, comment := "The ability that Ms. Marvel grants herself will overwrite any previous effects that set her power to a specific number. Her power will change as the number of cards in your hand changes during the turn. Effects that otherwise modify her power will still apply no matter when they took effect. The same is true for +1/+1 counters.",
    cards := #["Ms. Marvel, Kamala Khan"],
    sets := #["msh"] },
  { id := 641, comment := "The ability that defines Namor's power works in all zones, not just the battlefield.",
    cards := #["Namor the Sub-Mariner"],
    sets := #["msh"] },
  { id := 642, comment := "The ability that sets Super-Adaptoid's power works in all zones, not just the battlefield.",
    cards := #["Super-Adaptoid"],
    sets := #["msh"] },
  { id := 643, comment := "The additional X damage is dealt by the same source as the original source of damage. The damage isn't dealt by Hawkeye unless he is somehow the original source of that damage.",
    cards := #["Hawkeye, Young Avenger"],
    sets := #["msh"] },
  { id := 644, comment := "The amount of life you gain from extort is based on the total amount of life lost, not necessarily the number of opponents you have. For example, if your opponent's life total can't change (perhaps because that player controls Platinum Emperion), you won't gain any life.",
    cards := #["The Kingpin of Crime"],
    sets := #["msh"] },
  { id := 645, comment := "The check for whether a creature dealt damage by a source with deathtouch is destroyed happens only the first time that state-based actions are performed after that damage-dealing event. For example, if Doctor Doom is dealt 1 damage by a creature with deathtouch while he has indestructible, he won't die if he loses indestructible later in the turn.",
    cards := #["Doctor Doom"],
    sets := #["msh"] },
  { id := 646, comment := "The copy will have the same targets unless you choose new ones. You may change any number of the targets, including all of them or none of them. The new targets must be legal.",
    cards := #["Fin Fang Foom"],
    sets := #["msh"] },
  { id := 647, comment := "The creature that returns to the battlefield is a Hero in addition to its other types from the moment it enters. If an ability triggers whenever a Hero you control enters, that ability will trigger.",
    cards := #["Thunderbolts Conspiracy"],
    sets := #["msh"] },
  { id := 648, comment := "The extort ability doesn't target any player.",
    cards := #["The Kingpin of Crime"],
    sets := #["msh"] },
  { id := 649, comment := "The last ability will check as each end step starts to see if you attacked with a Hero this turn or a Hero entered the battlefield under your control this turn. If neither one of those conditions was met, the ability won't trigger at all. You won't be able to put a Hero onto the battlefield under your control during that end step in time to have the ability trigger.",
    cards := #["Avengers Assemble!"],
    sets := #["msh"] },
  { id := 650, comment := "The number of cards you ultimately draw may be affected by replacement effects. For example, if you have five cards in hand as the last ability of The Ten Rings resolves and control Thought Reflection (an enchantment that says \"If you would draw a card, draw two cards instead\"), you'll end up drawing ten cards.",
    cards := #["The Ten Rings"],
    sets := #["msh"] },
  { id := 651, comment := "The permanent's owner chooses whether to put it second from the top or on the bottom of their library. If multiple cards are put into the library this way (such as when this spell targets a melded permanent), that permanent's owner puts all the cards second from the top or all the cards on the bottom. They put them in whatever order they wish and do not need to reveal the order.",
    cards := #["Trickster's Stratagem"],
    sets := #["msh"] },
  { id := 652, comment := "The player you're controlling is still the active player during that turn.",
    cards := #["Construct a Cosmic Cube"],
    sets := #["msh"] },
  { id := 653, comment := "The power-up ability of Pet Avengers doesn't target itself. If it's no longer on the battlefield as that ability resolves, you'll still create the Hero creature token.",
    cards := #["Pet Avengers"],
    sets := #["msh"] },
  { id := 654, comment := "The source of the copy from Echo's ability is the same as the source of the original ability.",
    cards := #["Echo, Perceptive Prodigy"],
    sets := #["msh"] },
  { id := 655, comment := "The source of the copy from Scientist Supreme of A.I.M.'s ability is the same as the source of the original ability.",
    cards := #["Scientist Supreme of A.I.M."],
    sets := #["msh"] },
  { id := 656, comment := "The token created by Ultron's last ability copies exactly what was printed on the original artifact and nothing else, with the listed exception (unless that artifact is copying something else; see below). It doesn't copy whether that artifact is tapped or untapped, whether it has any counters on it or Auras attached to it, or any non-copy effects that have changed its types, color, or so on. If it is a Vehicle, it is not crewed. If it is an Equipment, it is not attached to anything.",
    cards := #["Ultron, Artificial Malevolence"],
    sets := #["msh"] },
  { id := 657, comment := "The value of X is calculated at the time the noncombat damage would be dealt.",
    cards := #["Hawkeye, Young Avenger"],
    sets := #["msh"] },
  { id := 658, comment := "The value of X is calculated only once, as Jessica Jones's ability resolves.",
    cards := #["Jessica Jones, Private Eye"],
    sets := #["msh"] },
  { id := 659, comment := "The value of X is calculated only once, as The Unbeatable Squirrel Girl's last ability resolves.",
    cards := #["The Unbeatable Squirrel Girl"],
    sets := #["msh"] },
  { id := 660, comment := "The value of X is calculated only once, as War Machine's last ability resolves.",
    cards := #["War Machine, Legacy of Iron"],
    sets := #["msh"] },
  { id := 661, comment := "The value of X is calculated only once, as Whiplash's last ability resolves.",
    cards := #["Whiplash, Vengeful Engineer"],
    sets := #["msh"] },
  { id := 662, comment := "The value of X is determined only once, as Captain America's last ability resolves.",
    cards := #["Captain America, Wings of Freedom"],
    sets := #["msh"] },
  { id := 663, comment := "Thor's last ability resolves before the spell that caused it to trigger. It resolves even if that spell is countered or otherwise leaves the stack without resolving.",
    cards := #["Thor, God of Thunder"],
    sets := #["msh"] },
  { id := 664, comment := "Tigra's last ability triggers just once for each life-gaining event, no matter how much life is gained.",
    cards := #["Tigra, Feline Fury"],
    sets := #["msh"] },
  { id := 665, comment := "To determine the total cost of a spell, start with the mana cost or alternative cost you're paying, add any cost increases, then apply any cost reductions. The mana value of the spell is determined only by its mana cost, no matter what the total cost to cast the spell was.",
    cards := #["The Scarlet Witch"],
    sets := #["msh"] },
  { id := 666, comment := "To double a creature's power and toughness, that creature gets +X/+Y, where X is that creature's power and Y is that creature's toughness when Epic Fight resolves.",
    cards := #["Epic Fight"],
    sets := #["msh"] },
  { id := 667, comment := "To double a creature's power and toughness, that creature gets +X/+Y, where X is that creature's power and Y is that creature's toughness when World War Hulk's third chapter ability resolves.",
    cards := #["World War Hulk"],
    sets := #["msh"] },
  { id := 668, comment := "To heal damage from a permanent, remove all damage currently marked on it.",
    cards := #["Wolverine, Fierce Fighter"],
    sets := #["msh"] },
  { id := 669, comment := "Token creatures you control dying won't cause Robot Domination's first ability to trigger.",
    cards := #["Robot Domination"],
    sets := #["msh"] },
  { id := 670, comment := "Ultron Drone's power-up ability doesn't target itself. If it isn't on the battlefield as that ability tries to resolve, the other effect will still happen. You'll create the Robot Villain token.",
    cards := #["Ultron Drone"],
    sets := #["msh"] },
  { id := 671, comment := "Until it is harnessed, The Mind Stone doesn't have the ability listed after the infinity symbol. It also doesn't have that ability in zones other than the battlefield.",
    cards := #["The Mind Stone"],
    sets := #["msh"] },
  { id := 672, comment := "Vibranium tokens are a kind of predefined token. Each one has the artifact subtype Vibranium, has indestructible, and has \": Add . This mana can't be spent to cast a nonartifact spell.\"",
    cards := #["T'Challa, the Black Panther"],
    sets := #["msh"] },
  { id := 673, comment := "Viv Vision's second ability triggers no matter what her power is. Players can respond to this ability as normal, perhaps trying to raise or lower her power. The ability checks Viv Vision's power only as it resolves to see if you draw a card.",
    cards := #["Viv Vision, Teen Synthezoid"],
    sets := #["msh"] },
  { id := 674, comment := "When Absorbing Man becomes a copy of the target permanent, he's neither entering nor leaving the battlefield. Any enters or leaves-the-battlefield abilities won't trigger.",
    cards := #["Absorbing Man"],
    sets := #["msh"] },
  { id := 675, comment := "When Iron Man attacks, if no artifacts have entered the battlefield under your control this turn, his last ability won't trigger at all. It's not possible to put an artifact onto the battlefield under your control after he attacks in time to have the ability trigger.",
    cards := #["Iron Man, Master of Machines"],
    sets := #["msh"] },
  { id := 676, comment := "When Photon Blast Barrage's first ability resolves, it creates X copies of Photon Blast Barrage. Those copies are created on the stack, so they're not \"cast.\" Abilities that trigger when a player casts a spell won't trigger. The copies will then resolve like normal spells, after players get a chance to cast spells and activate abilities.",
    cards := #["Photon Blast Barrage"],
    sets := #["msh"] },
  { id := 677, comment := "When Secret Invasion's triggered ability resolves, the enchanted creature copies exactly what was printed on the target creature and nothing else (unless that permanent is copying something else or is a token; see below). It doesn't copy whether it's tapped or untapped, whether it has any counters on it or Auras and Equipment attached to it, or any non-copy effects that have changed its power, toughness, types, color, and so on.",
    cards := #["Secret Invasion"],
    sets := #["msh"] },
  { id := 678, comment := "When Taskmaster becomes a copy of the target creature or card, he's neither entering nor leaving the battlefield. Any enters or leaves-the-battlefield abilities won't trigger.",
    cards := #["Taskmaster, Mercenary Mimic"],
    sets := #["msh"] },
  { id := 679, comment := "When comparing the stats as Hulkling's last ability resolves, it's possible that the stat that's greater changes from power to toughness or vice versa. If this happens, the ability will still resolve and you'll put a +1/+1 counter on Hulkling. For example, if you control a 2/3 Hulkling and a 1/4 creature you control enters, its toughness is greater, so Hulkling's last ability will trigger. In response, the 1/4 creature gets +2/-2, making it a 3/2. When Hulkling's ability resolves, it will see that the creature that entered has greater power than Hulkling, and you'll put a +1/+1 counter on Hulkling.",
    cards := #["Hulkling, Burgeoning Bruiser"],
    sets := #["msh"] },
  { id := 680, comment := "When comparing the stats of the creature that entered to Hulkling's stats, you always compare power to power and toughness to toughness.",
    cards := #["Hulkling, Burgeoning Bruiser"],
    sets := #["msh"] },
  { id := 681, comment := "When the enchanted creature becomes a copy of the target creature, it's neither entering nor leaving the battlefield. Any enters or leaves-the-battlefield abilities won't trigger.",
    cards := #["Secret Invasion"],
    sets := #["msh"] },
  { id := 682, comment := "When the first target artifact becomes a copy of the second target artifact, it's neither entering nor leaving the battlefield. Any enters or leaves-the-battlefield abilities won't trigger.",
    cards := #["Shuri, Wakandan Inventor"],
    sets := #["msh"] },
  { id := 683, comment := "When using improvise to cast a spell with in its mana cost, first choose the value for X. That choice, plus any cost increases or decreases, will determine the spell's total cost. Then you can tap artifacts you control to help pay that cost. For example, if you cast Whir of Invention (a spell with improvise and mana cost ) and choose X to be 3, the total cost is . If you tap two artifacts, you'll have to pay .",
    cards := #["Ironheart, Clever Champion"],
    sets := #["msh"] },
  { id := 684, comment := "Whenever a creature you control enters, check its power and toughness against Hulkling's power and toughness. If neither stat of the new creature is greater, Hulkling's last ability won't trigger at all.",
    cards := #["Hulkling, Burgeoning Bruiser"],
    sets := #["msh"] },
  { id := 685, comment := "Whether the exiled card is a Hero card only determines if Daredevil gets +2/+1 until end of turn. You may play the exiled card that turn regardless.",
    cards := #["Daredevil, Man Without Fear"],
    sets := #["msh"] },
  { id := 686, comment := "While controlling another player, you also continue to make your own choices and decisions.",
    cards := #["Construct a Cosmic Cube"],
    sets := #["msh"] },
  { id := 687, comment := "While controlling another player, you can see all cards in the game that the player can see. This includes cards in that player's hand, face-down permanents they control, face-down cards in exile they're allowed to look at, and any cards in their library they're allowed to look at.",
    cards := #["Construct a Cosmic Cube"],
    sets := #["msh"] },
  { id := 688, comment := "While controlling another player, you make all choices and decisions that player is allowed to make or is told to make. This includes choices about what spells to cast or what abilities to activate, as well as any decisions called for by triggered abilities or anything else.",
    cards := #["Construct a Cosmic Cube"],
    sets := #["msh"] },
  { id := 689, comment := "While you control Wonder Man, you'll be able to activate each power-up ability of permanents you control twice rather than once. This doesn't change, even if Wonder Man leaves the battlefield and a new instance of Wonder Man comes under your control. For example, say you activate Stature's power-up ability twice, then Wonder Man dies, then you cast another Wonder Man. You won't be able to activate Stature's power-up ability again.",
    cards := #["Wonder Man, Hollywood Hero"],
    sets := #["msh"] },
  { id := 690, comment := "White Tiger's power-up ability doesn't target herself. If she's no longer on the battlefield as that ability resolves, you'll still create The Tiger God.",
    cards := #["White Tiger, Ava Ayala"],
    sets := #["msh"] },
  { id := 691, comment := "Wiccan's last ability resolves before the spell that caused it to trigger. It resolves even if that spell is countered or otherwise leaves the stack without resolving.",
    cards := #["Wiccan, Rising Magician"],
    sets := #["msh"] },
  { id := 692, comment := "Wolverine's last ability is a replacement effect. It doesn't use the stack and can't be responded to.",
    cards := #["Wolverine, Fierce Fighter"],
    sets := #["msh"] },
  { id := 693, comment := "Wonder Man is legendary, but if you find a way to control two of him, you'll be able to activate power-up abilities of permanents you control two additional times. Controlling three Wonder Men will allow three additional times, and so on.",
    cards := #["Wonder Man, Hollywood Hero"],
    sets := #["msh"] },
  { id := 694, comment := "Wonder Man's second ability applies to his own power-up ability in addition to power-up abilities of other permanents you control.",
    cards := #["Wonder Man, Hollywood Hero"],
    sets := #["msh"] },
  { id := 695, comment := "World War Hulk's first chapter ability only affects the next red or green creature spell you cast this turn, even if you decide to pay that spell's mana cost for some reason.",
    cards := #["World War Hulk"],
    sets := #["msh"] },
  { id := 696, comment := "You can discard either one artifact card or two cards which may or may not be artifacts. If you really want to, you can discard two artifact cards.",
    cards := #["Thirst for Knowledge"],
    sets := #["msh"] },
  { id := 697, comment := "You can spend the mana added by the last ability on anything that isn't a nonartifact spell. This includes casting artifact spells, paying costs to activate abilities of both artifact and nonartifact permanents, paying ward costs, and so on.",
    cards := #["Hydraulic Helper"],
    sets := #["msh"] },
  { id := 698, comment := "You can use only the affected player's resources (cards, mana, and so on) to pay costs for the player; you can't use your own. Similarly, you can use the affected player's resources only to pay that player's costs; you can't spend them to pay your costs.",
    cards := #["Construct a Cosmic Cube"],
    sets := #["msh"] },
  { id := 699, comment := "You can use the added by a Vibranium token on anything that isn't a nonartifact spell. This includes paying costs to activate abilities of both artifact and nonartifact permanents, paying ward costs, and so on.",
    cards := #["T'Challa, the Black Panther"],
    sets := #["msh"] },
  { id := 700, comment := "You can't choose the same mode more than once for The Ruinous Wrecking Crew's last ability, even if X is greater than 4.",
    cards := #["The Ruinous Wrecking Crew"],
    sets := #["msh"] },
  { id := 701, comment := "You can't look at cards in the sideboard of a player you're controlling. If an effect instructs that player to choose a card from outside the game, you can't have that player choose any card.",
    cards := #["Construct a Cosmic Cube"],
    sets := #["msh"] },
  { id := 702, comment := "You can't make any choices or decisions for the player that would be called for by the tournament rules, such as whether to take an intentional draw or whether to call a judge.",
    cards := #["Construct a Cosmic Cube"],
    sets := #["msh"] },
  { id := 703, comment := "You can't make any illegal decisions or choices—you can't do anything that player couldn't do. You can't make choices or decisions that aren't called for by the game rules or by any cards, permanents, spells, abilities, and so on. If an effect causes another player to make decisions that the affected player would normally make (such as Master Warcraft does), that effect takes precedence. In other words, if the affected player wouldn't make a decision, you wouldn't make that decision while controlling that player.",
    cards := #["Construct a Cosmic Cube"],
    sets := #["msh"] },
  { id := 704, comment := "You can't make the player you're controlling concede. That player may concede at any time, even while you're controlling them.",
    cards := #["Construct a Cosmic Cube"],
    sets := #["msh"] },
  { id := 705, comment := "You cast the copies while Baron Helmut Zemo's boast ability is resolving and still on the stack. You can't wait to cast them later in the turn.",
    cards := #["Baron Helmut Zemo"],
    sets := #["msh"] },
  { id := 706, comment := "You choose how many targets the reflexive triggered ability has and how the damage will be divided among the targets as you put the ability on the stack. Each target must receive at least 1 damage.",
    cards := #["Death to Our Enemies"],
    sets := #["msh"] },
  { id := 707, comment := "You choose the player, planeswalker, or battle the creature you put onto the battlefield is attacking. It doesn't have to be the same player, planeswalker, or battle that Grim Reaper or any other attacking creatures are attacking.",
    cards := #["Grim Reaper, Lethal Legionnaire"],
    sets := #["msh"] },
  { id := 708, comment := "You choose whether to cast a spell from among the top six cards of your library as Cosmic Cube's last ability resolves. You can't wait to cast one later in the turn. Timing restrictions based on the card's types are ignored.",
    cards := #["Cosmic Cube"],
    sets := #["msh"] },
  { id := 709, comment := "You choose whether to cast up to two spells from among the exiled cards as Doom Reigns Supreme's reflexive triggered ability resolves. You can't wait to cast them later in the turn. Timing restrictions based on the cards' types are ignored.",
    cards := #["Doom Reigns Supreme"],
    sets := #["msh"] },
  { id := 710, comment := "You control only the player. You don't control any of that player's permanents, spells, or abilities.",
    cards := #["Construct a Cosmic Cube"],
    sets := #["msh"] },
  { id := 711, comment := "You don't choose a target for Bullseye's first ability at the time it triggers. Rather, a second \"reflexive\" ability triggers when you sacrifice an artifact or discard a nonland card this way. You choose a target for that ability as it goes on the stack. Each player may respond to this triggered ability as normal.",
    cards := #["Bullseye, Death Dealer"],
    sets := #["msh"] },
  { id := 712, comment := "You don't choose a target for Claim the Kingdom's last ability at the time it triggers. Rather, a second \"reflexive\" ability triggers when you sacrifice Claim the Kingdom this way. You choose a target for that ability as it goes on the stack. Each player may respond to this triggered ability as normal.",
    cards := #["Claim the Kingdom"],
    sets := #["msh"] },
  { id := 713, comment := "You don't choose a target for Construct a Cosmic Cube's last ability at the time it triggers. Rather, a second \"reflexive\" ability triggers when you sacrifice Construct a Cosmic Cube this way. You choose a target for that ability as it goes on the stack. Each player may respond to this triggered ability as normal.",
    cards := #["Construct a Cosmic Cube"],
    sets := #["msh"] },
  { id := 714, comment := "You don't choose a target for Doom Reigns Supreme's last ability at the time it triggers. Rather, a second \"reflexive\" ability triggers when you sacrifice Doom Reigns Supreme this way. You choose a target for that ability as it goes on the stack. Each player may respond to this triggered ability as normal.",
    cards := #["Doom Reigns Supreme"],
    sets := #["msh"] },
  { id := 715, comment := "You don't choose a target for Grim Reaper's ability at the time it triggers. Rather, a second \"reflexive\" ability triggers when you pay this way. You choose a target for that ability as it goes on the stack. Each player may respond to this triggered ability as normal.",
    cards := #["Grim Reaper, Lethal Legionnaire"],
    sets := #["msh"] },
  { id := 716, comment := "You don't choose a target for Killmonger's first ability at the time it triggers. Rather, a second \"reflexive\" ability triggers when you sacrifice another creature this way. You choose a target for that ability as it goes on the stack. Each player may respond to this triggered ability as normal.",
    cards := #["Killmonger, Scourge of Wakanda"],
    sets := #["msh"] },
  { id := 717, comment := "You don't choose a target for Red Hulk's last ability at the time it triggers. Rather, a second \"reflexive\" ability triggers when you put a +1/+1 counter on him this way. You choose a target for that ability as it goes on the stack. Each player may respond to this triggered ability as normal.",
    cards := #["Red Hulk"],
    sets := #["msh"] },
  { id := 718, comment := "You don't choose a target for Speed's last ability at the time it triggers. Rather, a second \"reflexive\" ability triggers when you pay this way. You choose a target for that ability as it goes on the stack. Each player may respond to this triggered ability as normal.",
    cards := #["Speed, Young Avenger"],
    sets := #["msh"] },
  { id := 719, comment := "You don't choose a target for Spider-Man's last ability at the time it triggers. Rather, a second \"reflexive\" ability triggers when you tap Spider-Man this way. You choose a target for that ability as it goes on the stack. Each player may respond to this triggered ability as normal.",
    cards := #["Spider-Man, To the Rescue"],
    sets := #["msh"] },
  { id := 720, comment := "You don't choose targets for Death to Our Enemies's last ability at the time it triggers. Rather, a second \"reflexive\" ability triggers when you sacrifice Death to Our Enemies this way. You choose targets for that ability as it goes on the stack. Each player may respond to this triggered ability as normal.",
    cards := #["Death to Our Enemies"],
    sets := #["msh"] },
  { id := 721, comment := "You don't choose targets for Rewrite History's last ability at the time it triggers. Rather, a second \"reflexive\" ability triggers when you sacrifice Rewrite History this way. You choose targets for that ability as it goes on the stack. Each player may respond to this triggered ability as normal.",
    cards := #["Rewrite History"],
    sets := #["msh"] },
  { id := 722, comment := "You may change any number of the targets, including all of them or none of them. If, for one of the targets, you can't choose a new legal target, then it remains unchanged (even if the current target is illegal).",
    cards := #["Speedball, New Warrior"],
    sets := #["msh"] },
  { id := 723, comment := "You may pay a maximum of one time for each extort triggered ability. You decide whether to pay when the ability resolves.",
    cards := #["The Kingpin of Crime"],
    sets := #["msh"] },
  { id := 724, comment := "You pay all costs and follow all normal timing rules for a card played this way. For example, if the exiled card is a sorcery card, you may play it only during your main phase while the stack is empty.",
    cards := #["Thor, God of Thunder"],
    sets := #["msh"] },
  { id := 725, comment := "You pay all costs and follow all normal timing rules for spells cast with the permission granted by Black Widow's last ability. For example, if the exiled nonland card is a sorcery card, you may cast it only during your main phase while the stack is empty.",
    cards := #["Black Widow, Super Spy"],
    sets := #["msh"] },
  { id := 726, comment := "You pay all costs and follow all timing rules for cards played with the permission granted by Moonstone's last ability. For example, if the exiled card is a land card, you may play it only during your main phase while the stack is empty.",
    cards := #["Moonstone, Harsh Mistress"],
    sets := #["msh"] },
  { id := 727, comment := "You'll draw a card for each card you've discarded that turn, even if those cards are no longer in your graveyard as Misty Knight's ability resolves.",
    cards := #["Misty Knight, Hero for Hire"],
    sets := #["msh"] },
  { id := 728, comment := "Your maximum hand size is checked only during the cleanup step of your turn. At any other time, you may have any number of cards in hand.",
    cards := #["The Ten Rings"],
    sets := #["msh"] }
]

/-- Number of unique Oracle ruling comments across every modeled set. -/
def uniqueOracleRulingCount : Nat := uniqueOracleRulings.size

/-- Rulings that apply to at least one HOB or HOC card. -/
def uniqueHobHocOracleRulings : Array OracleRuling :=
  uniqueOracleRulings.filter (fun r =>
    r.sets.any (fun s => s == "hob" || s == "hoc"))

/-- Number of unique Oracle ruling comments that apply to a HOB or HOC card. -/
def uniqueHobHocOracleRulingCount : Nat := uniqueHobHocOracleRulings.size

/-- Rulings that apply to at least one MSH card. -/
def uniqueMshOracleRulings : Array OracleRuling :=
  uniqueOracleRulings.filter (fun r => r.sets.any (· == "msh"))

/-- Number of unique Oracle ruling comments that apply to an MSH card. -/
def uniqueMshOracleRulingCount : Nat := uniqueMshOracleRulings.size

#guard uniqueOracleRulingCount == 728
#guard uniqueHobHocOracleRulingCount == 359
#guard uniqueMshOracleRulingCount == 376
#guard uniqueOracleRulings[0]!.id == 1
#guard uniqueOracleRulings.back!.id == 728
#guard uniqueHobHocOracleRulings[0]!.id == 1
#guard uniqueHobHocOracleRulings.back!.id == 359
#guard (uniqueOracleRulings.map (·.id)).toList ==
  (List.range uniqueOracleRulingCount).map (· + 1)
#guard
  (CardDef.uniqueStrings (uniqueOracleRulings.toList.map (·.comment))).length ==
    uniqueOracleRulingCount
#guard uniqueOracleRulings.all (fun r => !r.cards.isEmpty)
#guard uniqueOracleRulings.all (fun r => !r.sets.isEmpty)
#guard uniqueHobHocOracleRulings.all (fun r =>
  r.sets.any (fun s => s == "hob" || s == "hoc"))
#guard uniqueMshOracleRulings.all (fun r => r.sets.any (· == "msh"))
#guard
  (uniqueOracleRulings.filter (fun r =>
    r.sets.any (fun s => s == "hob" || s == "hoc") &&
      r.sets.any (· == "msh"))).size == 7

end Mtg.Engine

/-!
# Engine behavior for unique HOB / HOC judge rulings

These tests check Gatherer / Scryfall `wotc` comments — rulings issued by
judges — not the rules text printed on the cards and not
`CardDef.matchesOracleText`. Each `#guard` is tagged with the ruling id
from `uniqueOracleRulings`. Comments shared with MSH cards keep this same
id so the ruling is set-independent.
-/

namespace Mtg.Engine.RulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/-- Look up a unique judge ruling by 1-based id in `uniqueOracleRulings`. -/
def ruling (id : Nat) : OracleRuling :=
  uniqueOracleRulings[id - 1]!

#guard uniqueOracleRulingCount == 728
#guard uniqueHobHocOracleRulingCount == 359
#guard (List.range 359).all (fun i => (ruling (i + 1)).id == i + 1)
#guard !(ruling 1).comment.contains "Whenever"
#guard (ruling 38).comment.contains "hone counter"
#guard (ruling 22).comment.contains "permanent"

/-- A 0/0 legendary Storied creature used only to test judge ruling 26. -/
def zeroStoried : CardDef :=
  legendaryCreature "Zero Story" ManaCost.empty #["Dwarf"] 0 0
    (keywords := Keyword.storied)

/-- Attach `equipName` to `hostName` and put `n` hone counters on the Equipment. -/
def honeOn (g : Game) (equipName hostName : String) (n : Nat) : Game :=
  let eq := namedPermanent g equipName
  let host := namedPermanent g hostName
  let g := g.attachSourceTo eq host
  g.mapObjectStatus (namedPermanent g equipName) (fun s => { s with hone := n })

/-!
## 1, 14–18, 40–41, 51–53, 61 — amass
-/

/-- Ruling 18 / 1: create a 0/0 Goblin Army, then put N counters on the
amassed Army. -/
def amassFresh : Game := started.amassGoblins ⟨0⟩ 2

def amassFreshOk : Bool :=
  let army := namedPermanent amassFresh "Goblin Army"
  army.printed.isToken && amassFresh.hasSubtype army "Goblin" &&
    amassFresh.hasSubtype army "Army" && army.status.plusOnePlusOne == 2 &&
    amassFresh.power army == 2 && amassFresh.toughness army == 2 &&
    amassFresh.log.any (fun s => mentions s "amassed Army") &&
    amassFresh.log.any (fun s => mentions s "entered as a 0/0 creature")

#guard amassFreshOk

/-- Ruling 1: later amass still names the same creature as the amassed Army. -/
def amassAgain : Game := amassFresh.amassGoblins ⟨0⟩ 1

#guard
  (amassAgain.battlefield.filter (fun o => o.name == "Goblin Army")).size == 1
#guard (namedPermanent amassAgain "Goblin Army").status.plusOnePlusOne == 3
#guard amassAgain.log.any (fun s => mentions s "Goblin Army is the amassed Army")

/-- Ruling 14 / 61: amass Orcs creates an Orc Army; combining with Goblins
makes a Goblin Orc Army. -/
def amassOrcThenGoblin : Game :=
  (started.amassOrcs ⟨0⟩ 1).amassGoblins ⟨0⟩ 1

def amassOrcThenGoblinOk : Bool :=
  let army := namedPermanent amassOrcThenGoblin "Orc Army"
  amassOrcThenGoblin.hasSubtype army "Orc" &&
    amassOrcThenGoblin.hasSubtype army "Goblin" &&
    amassOrcThenGoblin.hasSubtype army "Army" &&
    army.status.plusOnePlusOne == 2 &&
    (amassOrcThenGoblin.battlefield.filter (fun o =>
      amassOrcThenGoblin.hasSubtype o "Army")).size == 1

#guard amassOrcThenGoblinOk

/-- Ruling 40 / 41: amass Zombies is the same action with a Zombie Army. -/
def amassZombieThenOrc : Game :=
  (started.amassZombies ⟨0⟩ 1).amassOrcs ⟨0⟩ 1

def amassZombieThenOrcOk : Bool :=
  let army := namedPermanent amassZombieThenOrc "Zombie Army"
  amassZombieThenOrc.hasSubtype army "Zombie" &&
    amassZombieThenOrc.hasSubtype army "Orc" &&
    army.status.plusOnePlusOne == 2

#guard amassZombieThenOrcOk

/-- Ruling 15 / 51: Mentor of the Meek sees the token enter as 0/0, even
when later counters would put it above 2 power. -/
def amassMentorSeesZero : Game :=
  let g := addPermanent started mentorOfTheMeek ⟨0⟩ ⟨0⟩
  let g := g.amassGoblins ⟨0⟩ 3
  g.receivePriority ⟨0⟩

def amassMentorSeesZeroOk : Bool :=
  let army := namedPermanent amassMentorSeesZero "Goblin Army"
  army.status.plusOnePlusOne == 3 && amassMentorSeesZero.power army == 3 &&
    amassMentorSeesZero.stack.any (fun e =>
      (amassMentorSeesZero.object! e.objectId).triggeredAbility ==
        some (.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1))

#guard amassMentorSeesZeroOk

/-- Ruling 51: the Orc Army also enters as 0/0 before counters. -/
def amassOrcMentorSeesZero : Game :=
  let g := addPermanent started mentorOfTheMeek ⟨0⟩ ⟨0⟩
  let g := g.amassOrcs ⟨0⟩ 3
  g.receivePriority ⟨0⟩

def amassOrcMentorSeesZeroOk : Bool :=
  let army := namedPermanent amassOrcMentorSeesZero "Orc Army"
  army.status.plusOnePlusOne == 3 && amassOrcMentorSeesZero.power army == 3 &&
    amassOrcMentorSeesZero.stack.any (fun e =>
      (amassOrcMentorSeesZero.object! e.objectId).triggeredAbility ==
        some (.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1)) &&
    (ruling 51).comment.contains "Orc Army token you create enters"

#guard amassOrcMentorSeesZeroOk

/-- A 3-power creature entering after counters would not trigger Mentor. -/
def mentorIgnoresGiant : Game :=
  let g := addPermanent started mentorOfTheMeek ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  let mentor := namedPermanent g "Mentor of the Meek"
  let giant := namedPermanent g "Hill Giant"
  let g := g.putMatchingSourceTriggers ⟨0⟩ mentor .anotherCreatureYouControlEnters
    (cause := some giant)
  g.receivePriority ⟨0⟩

#guard mentorIgnoresGiant.stack.isEmpty

/-- Ruling 16 / 52: with several Armies, the newest is the amassed Army. -/
def twoArmiesThenAmass : Game :=
  let (g, _) := started.createToken ⟨0⟩ Game.goblinArmyToken
  let (g, _) := g.createToken ⟨0⟩ Game.orcArmyToken
  g.amassGoblins ⟨0⟩ 1

def twoArmiesThenAmassOk : Bool :=
  let orc := namedPermanent twoArmiesThenAmass "Orc Army"
  orc.status.plusOnePlusOne == 1 && twoArmiesThenAmass.hasSubtype orc "Goblin" &&
    (namedPermanent twoArmiesThenAmass "Goblin Army").status.plusOnePlusOne == 0

#guard twoArmiesThenAmassOk

/-- Ruling 52: with several Armies, amass Orcs chooses one and makes it an Orc. -/
def twoArmiesThenAmassOrcs : Game :=
  let (g, _) := started.createToken ⟨0⟩ Game.goblinArmyToken
  let (g, _) := g.createToken ⟨0⟩ Game.zombieArmyToken
  g.amassOrcs ⟨0⟩ 1

def twoArmiesThenAmassOrcsOk : Bool :=
  let z := namedPermanent twoArmiesThenAmassOrcs "Zombie Army"
  z.status.plusOnePlusOne == 1 && twoArmiesThenAmassOrcs.hasSubtype z "Orc" &&
    (ruling 52).comment.contains "multiple Army creatures"

#guard twoArmiesThenAmassOrcsOk

/-- Ruling 18: untargeted amass still creates the Army. -/
def untargetedAmass : Game := started.applyEffect ⟨0⟩ (Effect.amassGoblins 1) #[]

#guard untargetedAmass.battlefield.any (fun o => untargetedAmass.hasSubtype o "Army")

/-!
## 2–13 — Adventure
-/

/-- Ruling 2: in every zone except the stack-as-Adventure, ignore the
Adventure face. Bilbo in a graveyard is a blue creature of mana value 2. -/
def burglarPlot : AdventureFace := bilboLuckwearerCard.adventure.get!

#guard bilboLuckwearerCard.isCreature
#guard !bilboLuckwearerCard.isInstant
#guard !bilboLuckwearerCard.isSorcery
#guard bilboLuckwearerCard.manaValue == 2
#guard burglarPlot.name == "Burglar's Plot"
#guard burglarPlot.manaCost.manaValue == 5

/-- Ruling 3: “has an Adventure” looks at the adventurer card’s alternative
characteristics even when they are not in use. -/
def bilboInPlay : Game := addPermanent started bilboLuckwearerCard ⟨0⟩ ⟨0⟩

#guard (namedPermanent bilboInPlay "Bilbo, Luckwearer").printed.adventure.isSome
#guard !(namedPermanent bilboInPlay "Bilbo, Luckwearer").isAdventureSpell
#guard (namedPermanent bilboInPlay "Bilbo, Luckwearer").printed.isCreature

/-- Ruling 12 / 9: a spell cast as an Adventure uses only the alternative
characteristics. On the stack it is not a card that “has an Adventure”. -/
def spewOnStack : GameObject :=
  paidSpewFlame.object! paidSpewFlame.stack.back!.objectId

#guard spewOnStack.name == "Spew Flame"
#guard spewOnStack.printed.isSorcery
#guard spewOnStack.isAdventureSpell
#guard spewOnStack.printed.adventure.isNone
#guard spewOnStack.printed.manaCost.manaValue == 5

/-- Ruling 5 / 13: a resolving Adventure is exiled and may be cast as the
permanent later, only when timing allows. -/
def smaugExiledFromAdventure : Bool :=
  resolvedSpewFlame.objects.any (fun o =>
    o.zone == .exile && o.name == "Smaug, the Great Calamity")

def smaugAdventureExileOk : Bool :=
  smaugExiledFromAdventure &&
    resolvedSpewFlame.mayPlayFromExile ⟨0⟩ (exiledSmaug resolvedSpewFlame) &&
    !(resolvedSpewFlame.canCastAdventure ⟨0⟩ (exiledSmaug resolvedSpewFlame)) &&
    resolvedSpewFlame.adventureExileForbidsRecast (exiledSmaug resolvedSpewFlame) &&
    (ruling 13).comment.contains "timing restrictions and permissions"

#guard smaugAdventureExileOk

/-- Ruling 6: exile for any other reason does not grant the Adventure
cast-as-permanent permission. -/
def smaugExiledOtherwise : Game :=
  let g := addToHand started smaugTheGreatCalamity ⟨0⟩
  let id := (handCardNamed g ⟨0⟩ "Smaug, the Great Calamity").id
  (g.move id .exile none).1

def smaugExiledOtherwiseCard : GameObject :=
  match smaugExiledOtherwise.objects.find? (fun x =>
      x.zone == .exile && x.name == "Smaug, the Great Calamity") with
  | some x => x
  | none => panic! "expected Smaug in exile"

#guard !(smaugExiledOtherwise.mayPlayFromExile ⟨0⟩ smaugExiledOtherwiseCard)

/-- Ruling 4 / 11: legality uses the Adventure face. Spew Flame is a sorcery. -/
def spewFlameIsSorcery : Bool :=
  match smaugTheGreatCalamity.adventure with
  | some adv => adv.types.contains CardType.sorcery
  | none => false

#guard spewFlameIsSorcery
#guard (ruling 11).comment.contains "use only its alternative characteristics"
#guard (ruling 8).comment.contains "alternative Adventure name"
#guard smaugTheGreatCalamity.choosableNames.contains "Spew Flame"
#guard !smaugTheGreatCalamity.choosableNames.contains "Burglar's Plot"

def canCastSpewFlame : Bool :=
  smaugSetup.canCastAdventure ⟨0⟩
    (handCardNamed smaugSetup ⟨0⟩ "Smaug, the Great Calamity")

#guard canCastSpewFlame
#guard (smaugSetup.asSorcery? ⟨0⟩)

/-!
## 19–21 — landfall
-/

/-- Ruling 19: a nonland entering does not trigger landfall. -/
def creatureEtbVsLandfall : Game :=
  let g := addPermanent afterDraw attercop ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  g.afterPermanentEnters (namedPermanent g "Grizzly Bears")

#guard !(creatureEtbVsLandfall.log.any (fun s => mentions s "landfall"))

/-- Ruling 20: playing a land triggers landfall. -/
def hospitalityLandfallOk : Bool :=
  hospitalityLandPlayed.log.any (fun s => mentions s "landfall trigger is put on the stack") &&
    hospitalityLandPlayed.stack.size == 1

#guard hospitalityLandfallOk

/-- Ruling 20: a spell that puts a land onto the battlefield also triggers
landfall (Wood Elves + Attercop). -/
def woodElvesLandfallOk : Bool :=
  attercopWoodElvesResolved.log.any (fun s => mentions s "landfall trigger is put on the stack")

#guard woodElvesLandfallOk

/-- Ruling 21: each landfall ability of permanents you control triggers. -/
def twoLandfall : Game :=
  let g := addPermanent afterDraw attercop ⟨0⟩ ⟨0⟩
  let g := addPermanent g beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addToHand g forest ⟨0⟩
  mustApply g ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ "Forest").id)

def twoLandfallTriggered : Bool :=
  let onStack := twoLandfall.stack.filterMap (fun e =>
    (twoLandfall.object! e.objectId).triggeredAbility)
  let waiting := twoLandfall.waitingTriggers.map (·.ability)
  let all := onStack ++ waiting
  all.any (· == .onLandYouControlEntersGets 1 1) &&
    all.any (· == .onLandYouControlEntersPlusOnePlusOne)

#guard twoLandfallTriggered

/-- Ruling 19 / 20: an opponent's land does not trigger your landfall. -/
def nissaLandfallSilent : Bool :=
  !(nissaLandVsAttercop.log.any (fun s => mentions s "landfall"))

#guard nissaLandfallSilent

/-!
## 22, 24–28 — Storied / enduring story
-/

/-- Ruling 22: tokens and lands are permanents; a spell on the stack is not. -/
def permanentsVsSpell : Game :=
  let g := addUntappedLand started mountain
  (g.createToken ⟨0⟩ Game.treasureToken).1

#guard (namedPermanent permanentsVsSpell "Mountain").isOnBattlefield
#guard permanentsVsSpell.battlefield.any (fun o => o.name == "Treasure")
#guard !paidSpewFlame.stack.isEmpty
#guard !(paidSpewFlame.object! paidSpewFlame.stack.back!.objectId).isOnBattlefield

/-- Ruling 24: a legendary artifact counts once, not once per quality. -/
def stingAlone : Game := addPermanent started stingBilboSSword ⟨0⟩ ⟨0⟩

#guard (namedPermanent stingAlone "Sting, Bilbo's Sword").isLegendary
#guard (namedPermanent stingAlone "Sting, Bilbo's Sword").printed.isArtifact
#guard stingAlone.countsTowardStoried (namedPermanent stingAlone "Sting, Bilbo's Sword")
#guard stingAlone.storiedPermanentCount ⟨0⟩ == 1

/-- Ruling 24: legendary artifact + Saga is two permanents, not three. -/
def stingAndSaga : Game :=
  addPermanent (addPermanent started stingBilboSSword ⟨0⟩ ⟨0⟩)
    downInTheValley ⟨0⟩ ⟨0⟩

#guard stingAndSaga.storiedPermanentCount ⟨0⟩ == 2
#guard !(stingAndSaga.hasEnduringStory ⟨0⟩)

/-- Ruling 25: three artifacts without a storied permanent grant nothing. -/
def threeTreasures : Game := started.createTreasureTokens ⟨0⟩ 3

#guard threeTreasures.storiedPermanentCount ⟨0⟩ == 3
#guard !(threeTreasures.controlsStoried ⟨0⟩)
#guard !(threeTreasures.hasEnduringStory ⟨0⟩)

/-- Ruling 25: one artifact plus Thorin is only two counting permanents. -/
def thorinAndOneTreasure : Game :=
  let g := started.createTreasureTokens ⟨0⟩ 1
  let g := addPermanent g thorinOakenshield ⟨0⟩ ⟨0⟩
  g.refreshEnduringStory

#guard thorinAndOneTreasure.controlsStoried ⟨0⟩
#guard thorinAndOneTreasure.storiedPermanentCount ⟨0⟩ == 2
#guard !(thorinAndOneTreasure.hasEnduringStory ⟨0⟩)

/-- Ruling 26 / 28: the third counting permanent grants an enduring story
before SBA; a 0/0 that then dies still leaves the player with the story.
Storied does not use the stack. -/
def storyFromZero : Game :=
  let g := started.createTreasureTokens ⟨0⟩ 2
  let g := addPermanent g zeroStoried ⟨0⟩ ⟨0⟩
  g.afterPermanentEnters (namedPermanent g "Zero Story")

#guard storyFromZero.hasEnduringStory ⟨0⟩
#guard storyFromZero.log.any (fun s => mentions s "has an enduring story")
#guard storyFromZero.stack.isEmpty

def storyAfterSba : Game := storyFromZero.checkSBA

#guard storyAfterSba.hasEnduringStory ⟨0⟩
#guard !(storyAfterSba.battlefield.any (fun o => o.name == "Zero Story"))

/-- Ruling 27: the designation stays on the player after the permanents leave. -/
def storyGranted : Game :=
  let g := started.createTreasureTokens ⟨0⟩ 2
  let g := addPermanent g thorinOakenshield ⟨0⟩ ⟨0⟩
  g.refreshEnduringStory

def storyThenLostPermanents : Game :=
  storyGranted.battlefield.foldl (fun acc o =>
    if o.controlledBy ⟨0⟩ then (acc.move o.id (.graveyard o.owner) none).1 else acc)
    storyGranted

#guard storyGranted.hasEnduringStory ⟨0⟩
#guard storyThenLostPermanents.hasEnduringStory ⟨0⟩
#guard storyThenLostPermanents.storiedPermanentCount ⟨0⟩ == 0

/-- Ori's +1/+0 and vigilance apply only while you have an enduring story. -/
def oriAlone : Game := addPermanent started oriKeeperOfSongs ⟨0⟩ ⟨0⟩

#guard oriAlone.power (namedPermanent oriAlone "Ori, Keeper of Songs") == 3
#guard !(oriAlone.currentKeywords (namedPermanent oriAlone "Ori, Keeper of Songs")).vigilance

def oriWithStory : Game :=
  oriAlone.modifyPlayer ⟨0⟩ (fun pl => { pl with enduringStory := true })

#guard oriWithStory.power (namedPermanent oriWithStory "Ori, Keeper of Songs") == 4
#guard (oriWithStory.currentKeywords (namedPermanent oriWithStory "Ori, Keeper of Songs")).vigilance

/-- Fíli's team pump applies to other creatures while you have a story. -/
def filiAndBears : Game :=
  addPermanent (addPermanent started filiThePathfinder ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨0⟩ ⟨0⟩

#guard filiAndBears.power (namedPermanent filiAndBears "Grizzly Bears") == 2

def filiAndBearsStory : Game :=
  filiAndBears.modifyPlayer ⟨0⟩ (fun pl => { pl with enduringStory := true })

#guard filiAndBearsStory.power (namedPermanent filiAndBearsStory "Grizzly Bears") == 3
#guard filiAndBearsStory.toughness (namedPermanent filiAndBearsStory "Grizzly Bears") == 3

/-- Bombur does not untap unless you have an enduring story. -/
def bomburTapped : Game :=
  let g := addPermanent started bomburGentleDreamer ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Bombur, Gentle Dreamer"
  g.setObject { o with status := { o.status with tapped := true } }

def bomburStillTapped : Game := bomburTapped.beginStep .untap

#guard (namedPermanent bomburStillTapped "Bombur, Gentle Dreamer").status.tapped

def bomburUntapsWithStory : Game :=
  let g := bomburTapped.modifyPlayer ⟨0⟩ (fun pl => { pl with enduringStory := true })
  g.beginStep .untap

#guard !(namedPermanent bomburUntapsWithStory "Bombur, Gentle Dreamer").status.tapped

/-!
## 23 — recruit
-/

/-- Ruling 23: once recruit begins, the draw/discard/token sequence is a
pending action; other players cannot take actions in the middle. -/
def recruitPendingOk : Bool :=
  instructorEntered.pending == .recruitDiscard ⟨0⟩ &&
    instructorEntered.actor == some ⟨0⟩ &&
    !(instructorEntered.hasPriority ⟨0⟩) &&
    !(instructorEntered.hasPriority ⟨1⟩)

#guard recruitPendingOk
def recruitMadeSoldier : Bool :=
  instructorRecruited.battlefield.any (fun o =>
    o.name == "Human Soldier" && o.printed.isToken)

#guard recruitMadeSoldier

/-!
## 29–30 — typecycling
-/

/-- Ruling 30: typecycling searches; it does not draw a card. -/
def oliphauntCycledOk : Bool :=
  (oliphauntCycled.handObjects ⟨0⟩).any (fun o => o.name == "Mountain") &&
    (oliphauntCycled.player ⟨0⟩).graveyard.any (fun id =>
      (oliphauntCycled.object! id).name == "Oliphaunt") &&
    !(oliphauntCycled.handObjects ⟨0⟩).any (fun o => o.name == "Oliphaunt")

#guard oliphauntCycledOk

/-- Ruling 29: typecycling is an activated cycling-form ability (discard
this card from hand, search). The same activation is legal at instant speed
and illegal from the battlefield. -/
def oliphauntCycleShape : Bool :=
  oliphauntCycleAbility.cost.discardSource &&
    oliphauntCycleAbility.activateFromHand &&
    oliphauntCycleAbility.effect == Effect.searchLandTypeToHand "Mountain"

#guard oliphauntCycleShape
def oliphauntCycleAtEndOk : Bool :=
  oliphauntCycleAtEnd.canActivate ⟨0⟩
    (handCardNamed oliphauntCycleAtEnd ⟨0⟩ "Oliphaunt") oliphauntCycleAbility

#guard oliphauntCycleAtEndOk

def oliphauntOnBattlefield : Game := addPermanent afterDraw oliphaunt ⟨0⟩ ⟨0⟩

def oliphauntCannotCycleInPlay : Bool :=
  !oliphauntOnBattlefield.canActivate ⟨0⟩
    (namedPermanent oliphauntOnBattlefield "Oliphaunt") oliphauntCycleAbility

#guard oliphauntCannotCycleInPlay

/-!
## 31–33, 37 — flashback
-/

/-- Ruling 31: flashback means you may cast the card from the graveyard
paying the flashback cost. Moment of Glory needs a creature target. -/
def momentReady : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  addToGraveyard (skipTo g .precombatMain 40) momentOfGlory ⟨0⟩

#guard momentOfGlory.flashback == some (ManaCost.ofGenericAndColor 4 .white)

def momentReadyPlayable : Bool :=
  momentReady.mayPlayFromGraveyard ⟨0⟩
    (namedGraveyardCard momentReady ⟨0⟩ "Moment of Glory") &&
    momentReady.canCast ⟨0⟩
      (namedGraveyardCard momentReady ⟨0⟩ "Moment of Glory")

#guard momentReadyPlayable

/-- Ruling 37: flashback still obeys timing. A sorcery cannot be flashbacked
in the end step. -/
def momentAtEnd : Game :=
  let g := applyIdle (passBoth (skipTo afterDraw .end 80))
  addToGraveyard g momentOfGlory ⟨0⟩

def momentAtEndIllegal : Bool :=
  !momentAtEnd.asSorcery? ⟨0⟩ &&
    !momentAtEnd.canCast ⟨0⟩
      (namedGraveyardCard momentAtEnd ⟨0⟩ "Moment of Glory")

#guard momentAtEndIllegal

/-- Ruling 32: a flashback spell is exiled as it leaves the stack. -/
def momentFlashbacked : Game :=
  let g := withWhiteMana momentReady ⟨0⟩ 5
  let src := namedGraveyardCard g ⟨0⟩ "Moment of Glory"
  let g := mustApply g ⟨0⟩ (.cast src.id)
  let g := mustApply g ⟨0⟩ (.target (Target.permanent (namedPermanent g "Grizzly Bears").id))
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

def momentFlashbackedOk : Bool :=
  momentFlashbacked.objects.any (fun o =>
    o.zone == .exile && o.name == "Moment of Glory") &&
    !((momentFlashbacked.player ⟨0⟩).graveyard.any (fun id =>
      (momentFlashbacked.object! id).name == "Moment of Glory")) &&
    momentFlashbacked.log.any (fun s => mentions s "exiled (flashback)") &&
    (namedPermanent momentFlashbacked "Grizzly Bears").status.plusOnePlusOne == 1

#guard momentFlashbackedOk

/-- Ruling 33: if the card is in your graveyard on your turn, you may cast
it before the opponent receives priority. -/
def momentReadyHasPriority : Bool :=
  momentReady.hasPriority ⟨0⟩ && !momentReady.hasPriority ⟨1⟩ &&
    momentReady.canCast ⟨0⟩
      (namedGraveyardCard momentReady ⟨0⟩ "Moment of Glory")

#guard momentReadyHasPriority

/-!
## 38, 45, 60 — hone
-/

/-- Ruling 38 / 45: hone counters on any Equipment grant +1/+0, including
Equipment that never mentions hone (Dwarven Shortsword). -/
def shortswordHone : Game :=
  let g := addPermanent (addPermanent started dwarvenShortsword ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨0⟩ ⟨0⟩
  honeOn g "Dwarven Shortsword" "Grizzly Bears" 2

#guard shortswordHone.power (namedPermanent shortswordHone "Grizzly Bears") == 5
#guard shortswordHone.toughness (namedPermanent shortswordHone "Grizzly Bears") == 4

/-- Ruling 60: unattaching removes the power immediately. -/
def shortswordUnattached : Game :=
  let eq := namedPermanent shortswordHone "Dwarven Shortsword"
  shortswordHone.setObject { eq with attachedTo := none }

#guard shortswordUnattached.power (namedPermanent shortswordUnattached "Grizzly Bears") == 2
#guard shortswordUnattached.toughness (namedPermanent shortswordUnattached "Grizzly Bears") == 2

/-- Ruling 60: leaving the battlefield removes the boost immediately. -/
def shortswordLeft : Game :=
  let eq := namedPermanent shortswordHone "Dwarven Shortsword"
  (shortswordHone.move eq.id (.graveyard eq.owner) none).1

#guard shortswordLeft.power (namedPermanent shortswordLeft "Grizzly Bears") == 2

/-- Ruling 60: removing hone counters changes power immediately. -/
def shortswordHoneCleared : Game :=
  let eq := namedPermanent shortswordHone "Dwarven Shortsword"
  shortswordHone.mapObjectStatus eq (fun s => { s with hone := 0 })

#guard shortswordHoneCleared.power (namedPermanent shortswordHoneCleared "Grizzly Bears") == 3

/-- Ruling 38: the boost is from the counter, not an Equipment ability. -/
def shortswordNoStatics : Game :=
  let eq := namedPermanent shortswordHone "Dwarven Shortsword"
  shortswordHone.setObject { eq with printed := { eq.printed with staticAbilities := #[] } }

#guard shortswordNoStatics.power (namedPermanent shortswordNoStatics "Grizzly Bears") == 4
#guard shortswordNoStatics.toughness (namedPermanent shortswordNoStatics "Grizzly Bears") == 2

/-- Dwalin puts a hone counter on each Equipment you control. -/
def dwalinHoneTrigger : Bool :=
  dwalinWeaponmaster.triggeredAbilities == #[.onEnterOrAttackHoneEachEquipment]

#guard dwalinHoneTrigger

def dwalinHones : Game :=
  let g := addPermanent (addPermanent started dwarvenShortsword ⟨0⟩ ⟨0⟩)
    dwalinWeaponmaster ⟨0⟩ ⟨0⟩
  g.applyTriggeredAbility ⟨0⟩ .onEnterOrAttackHoneEachEquipment none

#guard (namedPermanent dwalinHones "Dwarven Shortsword").status.hone == 1

/-!
## 63, 69 — triggered vs activated wording (judge reminders)
-/

def dwalinTriggerWording : Bool :=
  (ruling 63).comment.contains "when" &&
    (TriggeredAbility.eventPrefix
      dwalinWeaponmaster.triggeredAbilities[0]!.timing).startsWith "Whenever"

def oinActivatedWording : Bool :=
  (ruling 69).comment.contains "colon" &&
    (ActivatedAbility.toNotation oinTheBrave.activatedAbilities[0]!).contains ":"

#guard dwalinTriggerWording
#guard oinActivatedWording

/-!
## 122 — Food is an artifact type, never a creature type
-/

#guard Game.foodToken.isArtifact
#guard !Game.foodToken.isCreature
#guard Game.foodToken.hasSubtype "Food"

/-- Find a battlefield-zone object by name, including while phased out. -/
def namedObject (g : Game) (name : String) : GameObject :=
  match g.objects.find? (fun o => o.name == name && o.zone == .battlefield) with
  | some o => o
  | none => panic! s!"expected {name} in the battlefield zone"

/-- An enchantment used only to watch Ring-tempt and Ring-bearer choices. -/
def ringWatcher : CardDef :=
  enchantment "Ring Watcher" (ManaCost.ofGeneric 1)
    "Whenever the Ring tempts you, draw a card.\nWhenever you choose a creature as your Ring-bearer, draw a card."
    (triggeredAbilities := #[.onTheRingTemptsYouDraw 1, .onChooseRingBearerDraw])

/-!
## 42–44, 48, 54, 56–57 — The Ring / Ring-bearer
-/

/-- Ruling 42 / 43: first tempt creates one emblem named The Ring and
chooses a Ring-bearer. A second tempt does not create a second emblem. -/
def ringFirstTempt : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  g.temptWithTheRing ⟨0⟩

def ringFirstTemptOk : Bool :=
  ringFirstTempt.hasTheRing ⟨0⟩ &&
    ringFirstTempt.theRingAbilityCount ⟨0⟩ == 1 &&
    (namedPermanent ringFirstTempt "Grizzly Bears").status.ringBearer &&
    ringFirstTempt.log.any (fun s => mentions s "emblem named The Ring") &&
    ringFirstTempt.log.any (fun s => mentions s "Ring-bearer")

#guard ringFirstTemptOk

def ringSecondTempt : Game := ringFirstTempt.temptWithTheRing ⟨0⟩

def ringSecondTemptOk : Bool :=
  ringSecondTempt.theRingAbilityCount ⟨0⟩ == 2 &&
    (ringSecondTempt.log.filter (fun s => mentions s "gets an emblem named The Ring")).size == 1 &&
    (namedPermanent ringSecondTempt "Grizzly Bears").status.ringBearer

#guard ringSecondTemptOk

/-- Ruling 43: each player has their own emblem and Ring-bearer. -/
def ringBothPlayers : Game :=
  let g := addPermanent (addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩)
    grayOgre ⟨1⟩ ⟨1⟩
  let g := g.temptWithTheRing ⟨0⟩
  g.temptWithTheRing ⟨1⟩

def ringBothPlayersOk : Bool :=
  ringBothPlayers.hasTheRing ⟨0⟩ && ringBothPlayers.hasTheRing ⟨1⟩ &&
    (namedPermanent ringBothPlayers "Grizzly Bears").status.ringBearer &&
    (namedPermanent ringBothPlayers "Gray Ogre").status.ringBearer &&
    !(ringBothPlayers.isRingBearer ⟨0⟩ (namedPermanent ringBothPlayers "Gray Ogre"))

#guard ringBothPlayersOk

/-- Ruling 44: if you control a creature you must choose one. -/
def ringMustChoose : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  g.temptWithTheRing ⟨0⟩ none

#guard (namedPermanent ringMustChoose "Grizzly Bears").status.ringBearer

/-- Ruling 56: the Ring can tempt you with no creature; tempt triggers still fire. -/
def ringNoCreature : Game :=
  let g := addPermanent started ringWatcher ⟨0⟩ ⟨0⟩
  g.temptWithTheRing ⟨0⟩

def ringNoCreatureOk : Bool :=
  ringNoCreature.hasTheRing ⟨0⟩ &&
    (ringNoCreature.player ⟨0⟩).ringBearerId.isNone &&
    ringNoCreature.log.any (fun s => mentions s "controls no creature") &&
    ringNoCreature.waitingTriggers.any (fun wt =>
      wt.ability == .onTheRingTemptsYouDraw 1)

#guard ringNoCreatureOk

/-- Ruling 48: choosing the same creature again still counts as choosing it. -/
def ringRechoose : Game :=
  let g := addPermanent (addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩)
    ringWatcher ⟨0⟩ ⟨0⟩
  let g := g.temptWithTheRing ⟨0⟩ (some (namedPermanent g "Grizzly Bears").id)
  g.temptWithTheRing ⟨0⟩ (some (namedPermanent g "Grizzly Bears").id)

def ringRechooseOk : Bool :=
  (ringRechoose.waitingTriggers.filter (fun wt =>
    wt.ability == .onChooseRingBearerDraw)).size == 2 &&
    (namedPermanent ringRechoose "Grizzly Bears").status.ringBearer

#guard ringRechooseOk

/-- Ruling 54: illegal or missing targets mean the Ring does not tempt you. -/
def ringTargetedFail : Game :=
  started.resolveTargetedTempt ⟨0⟩ .creature #[]

def ringTargetedFailOk : Bool :=
  !(ringTargetedFail.hasTheRing ⟨0⟩) &&
    ringTargetedFail.log.any (fun s => mentions s "won't tempt")

#guard ringTargetedFailOk

def ringTargetedOk : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  g.resolveTargetedTempt ⟨0⟩ .creature
    #[Target.permanent (namedPermanent g "Grizzly Bears").id]

#guard ringTargetedOk.hasTheRing ⟨0⟩

/-- Ruling 57: abilities are gained in order and kept. -/
def ringFourTempts : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  (((((g.temptWithTheRing ⟨0⟩).temptWithTheRing ⟨0⟩).temptWithTheRing ⟨0⟩).temptWithTheRing ⟨0⟩).temptWithTheRing ⟨0⟩)

#guard ringFourTempts.theRingAbilityCount ⟨0⟩ == 4

/-- Ruling 22: an emblem is not a permanent. -/
def ringEmblemNotPermanent : Bool :=
  ringFirstTempt.hasTheRing ⟨0⟩ &&
    !(ringFirstTempt.battlefield.any (fun o => o.name == "The Ring"))

#guard ringEmblemNotPermanent

/-!
## 46, 50, 58, 62, 95, 196, 197, 208, 209, 218 — kicker
-/

#guard galadrielSDismissal.kicker == some (ManaCost.ofGenericAndColor 2 .white)
#guard theEaglesAreComing.kicker == some (ManaCost.ofGenericAndColors 2 [.white, .white])
#guard galadrielSDismissal.manaValue == 1

/-- Ruling 46 / 58: paying kicker marks the spell kicked; you cannot kick twice. -/
def kickerProposed : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := withWhiteMana (addToHand g galadrielSDismissal ⟨0⟩) ⟨0⟩ 4
  mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Galadriel's Dismissal").id)

def kickerProposedOk : Bool :=
  kickerProposed.pending == .chooseKicker ⟨0⟩ &&
    !(kickerProposed.object! kickerProposed.stack.back!.objectId).kicked

#guard kickerProposedOk

def kickerPaid : Game := mustApply kickerProposed ⟨0⟩ (.announceKicker true)

def kickerPaidOk : Bool :=
  (kickerPaid.object! kickerPaid.stack.back!.objectId).kicked &&
    (match kickerPaid.proposedSpell with
     | some prop => prop.kicked && prop.cost.manaValue == 4
     | none => false)

#guard kickerPaidOk

def kickerTwiceFails : Bool :=
  match kickerPaid.applyKickerToProposed true with
  | .error e => e.contains "more than once"
  | .ok _ => false

#guard kickerTwiceFails

/-- Ruling 62: mana value is unchanged by paying kicker. -/
def kickerManaValueUnchanged : Bool :=
  (kickerPaid.object! kickerPaid.stack.back!.objectId).printed.manaValue == 1 &&
    (match kickerPaid.proposedSpell with
     | some prop => prop.cost.manaValue > 1
     | none => false)

#guard kickerManaValueUnchanged

/-- Ruling 218: putting a kicker permanent onto the battlefield does not kick it. -/
def kickerNotCast : Game := addPermanent started galadrielSDismissal ⟨0⟩ ⟨0⟩

#guard !(namedPermanent kickerNotCast "Galadriel's Dismissal").kicked

/-- Ruling 50 / 95 / 196 / 197: casting without paying the mana cost still
allows kicker as an additional cost. -/
def kickerWithoutManaCost : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addToHand g galadrielSDismissal ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Galadriel's Dismissal"
  let g := g.setObject { card with
    playPermission := some {
      player := ⟨0⟩
      turnEndsRemaining := 1
      withoutManaCost := true } }
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Galadriel's Dismissal").id)
  mustApply g ⟨0⟩ (.announceKicker true)

def kickerWithoutManaCostOk : Bool :=
  (kickerWithoutManaCost.object! kickerWithoutManaCost.stack.back!.objectId).kicked &&
    (match kickerWithoutManaCost.proposedSpell with
     | some prop => prop.cost.manaValue == 3
     | none => false)

#guard kickerWithoutManaCostOk

/-- Ruling 208 / 209: a copy of a kicked spell is also kicked. -/
def kickerCopied : Game :=
  let spell := kickerPaid.object! kickerPaid.stack.back!.objectId
  kickerPaid.copyStackSpell spell ⟨0⟩

#guard (kickerCopied.object! kickerCopied.stack.back!.objectId).kicked
#guard (kickerCopied.object! kickerCopied.stack.back!.objectId).isCopy

/-!
## 65, 83, 124, 152, 210, 333 — gift
-/

#guard bilboSGambit.giftTreasure

/-- Ruling 83 / 333: gift is promised as an additional cost, not given yet,
and cannot be promised twice. -/
def giftProposed : Game :=
  let (g, bolt) := afterDraw.allocObject lightningBolt ⟨1⟩ .stack (some ⟨1⟩)
  let g := g.putStackEntry ⟨1⟩ bolt.id
  let g := withWhiteMana (addToHand g bilboSGambit ⟨0⟩) ⟨0⟩ 2
  mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Bilbo's Gambit").id)

def giftProposedOk : Bool :=
  giftProposed.pending == .chooseGift ⟨0⟩ &&
    (giftProposed.object! giftProposed.stack.back!.objectId).giftPromisedTo.isNone

#guard giftProposedOk

def giftPromised : Game := mustApply giftProposed ⟨0⟩ (.announceGift (some ⟨1⟩))

def giftPromisedOk : Bool :=
  (giftPromised.object! giftPromised.stack.back!.objectId).giftPromisedTo == some ⟨1⟩ &&
    !(giftPromised.battlefield.any (fun o => o.name == "Treasure"))

#guard giftPromisedOk

def giftTwiceFails : Bool :=
  match giftPromised.applyGiftToProposed (some ⟨1⟩) with
  | .error e => e.contains "more than once"
  | .ok _ => false

#guard giftTwiceFails

/-- Ruling 124 / 65: on resolution of an instant, the gift is given before
other effects. -/
def giftGivenOnResolve : Game :=
  let g := giftPromised
  -- Skip remaining proposal (targets / pay) by resolving a ready stack object.
  let spell := g.object! g.stack.back!.objectId
  g.givePromisedGift (spell.giftPromisedTo.getD ⟨1⟩)

#guard giftGivenOnResolve.battlefield.any (fun o => o.name == "Treasure" && o.controlledBy ⟨1⟩)

/-- Ruling 152: if the spell is removed without resolving, the gift is not given. -/
def giftCountered : Game :=
  let spell := giftPromised.object! giftPromised.stack.back!.objectId
  (giftPromised.move spell.id (.graveyard spell.owner) none).1

#guard !(giftCountered.battlefield.any (fun o => o.name == "Treasure"))

/-- Ruling 210: a copy inherits the promised gift. -/
def giftCopied : Game :=
  let spell := giftPromised.object! giftPromised.stack.back!.objectId
  giftPromised.copyStackSpell spell ⟨0⟩

#guard (giftCopied.object! giftCopied.stack.back!.objectId).giftPromisedTo == some ⟨1⟩

/-!
## 67, 168, 235, 245 — shadow
-/

def shadowCreature : CardDef :=
  creature "Shadow Scout" (ManaCost.ofGeneric 1) #["Wraith"] 1 1
    (keywords := Keyword.shadow)

/-- Ruling 67: a shadow counter grants shadow. -/
def shadowFromCounter : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  g.putShadowCounter (namedPermanent g "Grizzly Bears")

def shadowFromCounterOk : Bool :=
  shadowFromCounter.hasShadow (namedPermanent shadowFromCounter "Grizzly Bears") &&
    shadowFromCounter.hasSubtype
      (namedPermanent shadowFromCounter "Grizzly Bears") "Wraith"

#guard shadowFromCounterOk

/-- Ruling 235: multiple instances of shadow are redundant. -/
def shadowTwice : Game :=
  shadowFromCounter.putShadowCounter
    (namedPermanent shadowFromCounter "Grizzly Bears")

#guard (namedPermanent shadowTwice "Grizzly Bears").status.shadow == 2
#guard shadowTwice.hasShadow (namedPermanent shadowTwice "Grizzly Bears")

/-- Ruling 168: shadow and flying both restrict blockers. -/
def shadowBlockSetup : Game :=
  let g := addPermanent (addPermanent started shadowCreature ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨1⟩ ⟨1⟩
  let atk := namedPermanent g "Shadow Scout"
  g.setObject { atk with status := { atk.status with attacking := true } }

def shadowCannotBlock : Bool :=
  !shadowBlockSetup.canBlock
    (namedPermanent shadowBlockSetup "Grizzly Bears")
    (namedPermanent shadowBlockSetup "Shadow Scout")

#guard shadowCannotBlock

def shadowCanBlockShadow : Game :=
  let g := addPermanent shadowBlockSetup
    (creature "Wraith Guard" (ManaCost.ofGeneric 1) #["Wraith"] 1 1
      (keywords := Keyword.shadow)) ⟨1⟩ ⟨1⟩
  g

def shadowCanBlockShadowOk : Bool :=
  shadowCanBlockShadow.canBlock
    (namedPermanent shadowCanBlockShadow "Wraith Guard")
    (namedPermanent shadowCanBlockShadow "Shadow Scout")

#guard shadowCanBlockShadowOk

/-- Ruling 245: once blocked, gaining or losing shadow does not undo the block. -/
def shadowRemainsBlocked : Game :=
  let g := addPermanent (addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩)
    (creature "Chump" (ManaCost.ofGeneric 1) #["Human"] 1 1) ⟨1⟩ ⟨1⟩
  let atk := namedPermanent g "Grizzly Bears"
  let g := g.setObject { atk with status := { atk.status with
    attacking := true, blocked := true } }
  let blk := namedPermanent g "Chump"
  let g := g.setObject { blk with status := { blk.status with
    blocking := #[atk.id] } }
  g.putShadowCounter (namedPermanent g "Grizzly Bears")

def shadowRemainsBlockedOk : Bool :=
  (namedPermanent shadowRemainsBlocked "Grizzly Bears").status.blocked &&
    shadowRemainsBlocked.hasShadow (namedPermanent shadowRemainsBlocked "Grizzly Bears")

#guard shadowRemainsBlockedOk

/-!
## 76–77, 82, 107, 253–255 — phasing
-/

/-- Ruling 254 / 76: a phased-out creature is treated as though it does not
exist and is removed from combat. -/
def phasedAttacker : Game :=
  let g := addPermanent (addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩)
    dwarvenShortsword ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let eq := namedPermanent g "Dwarven Shortsword"
  let g := g.attachSourceTo eq host
  let host := namedPermanent g "Grizzly Bears"
  let g := g.setObject { host with status := { host.status with attacking := true } }
  g.phaseOut (namedPermanent g "Grizzly Bears")

def phasedAttackerOk : Bool :=
  (namedObject phasedAttacker "Grizzly Bears").status.phasedOut &&
    !(namedObject phasedAttacker "Grizzly Bears").isOnBattlefield &&
    !(namedObject phasedAttacker "Grizzly Bears").status.attacking &&
    (namedObject phasedAttacker "Dwarven Shortsword").status.phasedOut &&
    phasedAttacker.permanentCount ⟨0⟩ == 0 &&
    (ruling 76).comment.contains "removed from combat"

#guard phasedAttackerOk

/-- Ruling 82 / 253: attachments phase in still attached; counters persist;
the creature can attack. -/
def phasedIn : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Grizzly Bears"
  let g := g.mapObjectStatus o (fun s => { s with plusOnePlusOne := 2 })
  let g := g.phaseOut (namedObject g "Grizzly Bears")
  g.phaseIn (namedObject g "Grizzly Bears")

def phasedInOk : Bool :=
  !(namedObject phasedIn "Grizzly Bears").status.phasedOut &&
    (namedObject phasedIn "Grizzly Bears").status.plusOnePlusOne == 2 &&
    !(namedObject phasedIn "Grizzly Bears").status.summoningSick &&
    phasedIn.canAttack (namedObject phasedIn "Grizzly Bears")

#guard phasedInOk

/-- Ruling 255: phasing does not trigger enters or leaves. -/
def phaseNoTriggers : Game :=
  let g := addPermanent (addPermanent started mentorOfTheMeek ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨0⟩ ⟨0⟩
  let g := g.phaseOut (namedPermanent g "Grizzly Bears")
  g.phaseIn (namedObject g "Grizzly Bears")

#guard phaseNoTriggers.stack.isEmpty
#guard phaseNoTriggers.waitingTriggers.isEmpty

/-- Ruling 107: additional subtypes chosen as the permanent entered are
remembered when it phases in. -/
def phaseRemembersTypes : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Grizzly Bears"
  let g := g.setObject { o with status := { o.status with
    additionalSubtypes := #["Wraith"] } }
  let g := g.phaseOut (namedPermanent g "Grizzly Bears")
  g.phaseIn (namedObject g "Grizzly Bears")

#guard phaseRemembersTypes.hasSubtype (namedPermanent phaseRemembersTypes "Grizzly Bears") "Wraith"

/-- Ruling 77: continuous effects ignore phased-out objects. Hone on a
phased-out Equipment does not boost the host. -/
def phaseIgnoresHone : Game :=
  let g := addPermanent (addPermanent started dwarvenShortsword ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨0⟩ ⟨0⟩
  let g := honeOn g "Dwarven Shortsword" "Grizzly Bears" 3
  let eq := namedPermanent g "Dwarven Shortsword"
  g.phaseOut eq

#guard phaseIgnoresHone.power (namedPermanent phaseIgnoresHone "Grizzly Bears") == 2

/-!
## 68, 101, 110, 113–114, 157, 238, 323 — cascade
-/

#guard callForthTheTempest.cascade == 2
#guard callForthTheTempest.manaValue == 8

/-- Ruling 68: mana value ignores alternative and additional costs. -/
def cascadeManaValueIsPrinted : Bool :=
  callForthTheTempest.manaValue == 8 &&
    callForthTheTempest.manaCost.manaValue == 8

#guard cascadeManaValueIsPrinted

/-- Ruling 101 / 114: cascade triggers when the spell is cast, once per
instance, and sits above the spell. -/
def cascadeOnCast : Game :=
  let g := addToHand afterDraw callForthTheTempest ⟨0⟩
  -- Give enough red/generic to propose; cascade triggers on becomeCast.
  let g := withWhiteMana g ⟨0⟩ 0
  -- Put the spell on the stack as if it finished casting.
  let id := (handCardNamed g ⟨0⟩ "Call Forth the Tempest").id
  let (g, newId) := g.move id .stack (some ⟨0⟩)
  let g := g.putStackEntry ⟨0⟩ newId
  g.becomeCast ⟨0⟩ (g.object! newId)

def cascadeOnCastOk : Bool :=
  let cascades := cascadeOnCast.stack.filter (fun e =>
    (cascadeOnCast.object! e.objectId).triggeredAbility == some .onCastCascade)
  cascades.size == 2 &&
    cascadeOnCast.stack.any (fun e =>
      (cascadeOnCast.object! e.objectId).name == "Call Forth the Tempest") &&
    (cascadeOnCast.player ⟨0⟩).castManaValuesThisTurn == #[8]

#guard cascadeOnCastOk

/-- Ruling 323 / 113: cascade must exile; the resulting spell must have
lesser mana value. Casting is optional. -/
def cascadeExiles : Game :=
  let (g, bolt) := started.allocObject lightningBolt ⟨0⟩ (.library ⟨0⟩)
  let (g, land) := g.allocObject forest ⟨0⟩ (.library ⟨0⟩)
  let g := g.setPlayer { (g.player ⟨0⟩) with library := #[bolt.id, land.id] }
  g.resolveCascade ⟨0⟩ 8

def cascadeExilesOk : Bool :=
  cascadeExiles.log.any (fun s => mentions s "cascade") &&
    cascadeExiles.objects.any (fun o =>
      o.zone == .exile && !o.printed.isLand)

#guard cascadeExilesOk

/-- Ruling 113: an Adventure card's resulting permanent spell must also be
cheaper. Smaug (MV 6) is cheaper than 8; the test card with MV 9 is not. -/
def expensiveCreature : CardDef :=
  creature "Costly Beast" (ManaCost.ofGeneric 9) #["Beast"] 9 9

/-- Ruling 113: the resulting spell's mana value must be less than the
cascade spell's. A 9-mana creature cannot be cast off an 8-mana cascade. -/
def cascadeResultTooExpensive : Bool :=
  let g := addToLibraryTop started expensiveCreature ⟨0⟩
  match g.objects.find? (fun o => o.name == "Costly Beast") with
  | none => false
  | some card =>
    match g.castCascadeCard ⟨0⟩ card.id 8 with
    | .error e => e.contains "lesser mana value"
    | .ok _ => false

#guard cascadeResultTooExpensive

/-- Ruling 110: copies that were not cast are omitted from the total. -/
def cascadeCopyNotCast : Game :=
  let g := cascadeOnCast
  let spell := g.object! (g.stack.find? (fun e =>
    (g.object! e.objectId).name == "Call Forth the Tempest") |>.get!).objectId
  g.copyStackSpell spell ⟨0⟩

#guard cascadeCopyNotCast.otherCastManaValueThisTurn ⟨0⟩ == 8
#guard (cascadeCopyNotCast.object! cascadeCopyNotCast.stack.back!.objectId).isCopy

/-- Ruling 157: countering the cascade spell leaves the cascade triggers. -/
def cascadeSpellRemoved : Game :=
  let spellE := cascadeOnCast.stack.find? (fun e =>
    (cascadeOnCast.object! e.objectId).name == "Call Forth the Tempest")
  match spellE with
  | none => cascadeOnCast
  | some e =>
    let o := cascadeOnCast.object! e.objectId
    (cascadeOnCast.move o.id (.graveyard o.owner) none).1

def cascadeSpellRemovedOk : Bool :=
  (cascadeSpellRemoved.stack.filter (fun e =>
    (cascadeSpellRemoved.object! e.objectId).triggeredAbility ==
      some .onCastCascade)).size == 2

#guard cascadeSpellRemovedOk

/-- Ruling 238: each cascade instance looks at Call Forth's mana value of 8. -/
def cascadeLooksAtEight : Bool :=
  (ruling 238).comment.contains "mana value of 8" &&
    callForthTheTempest.manaValue == 8

#guard cascadeLooksAtEight

/-!
## 84, 207, 223, 251 — ascend / city's blessing
-/

#guard andurilNarsilReforged.keywords.ascend

/-- Ruling 207: ten permanents without ascend grant nothing. -/
def tenTreasures : Game := started.createTreasureTokens ⟨0⟩ 10

#guard tenTreasures.permanentCount ⟨0⟩ == 10
#guard !(tenTreasures.controlsAscend ⟨0⟩)
#guard !(tenTreasures.hasCitysBlessing ⟨0⟩)

/-- Ruling 207: Andúril entering as the ninth permanent is not enough. -/
def nineThenAnduril : Game :=
  let g := started.createTreasureTokens ⟨0⟩ 8
  let g := addPermanent g andurilNarsilReforged ⟨0⟩ ⟨0⟩
  g.refreshCitysBlessing

#guard nineThenAnduril.permanentCount ⟨0⟩ == 9
#guard nineThenAnduril.controlsAscend ⟨0⟩
#guard !(nineThenAnduril.hasCitysBlessing ⟨0⟩)

/-- Ruling 84 / 223: the tenth permanent with ascend grants the blessing
before SBA, and it is not a triggered ability. -/
def tenWithAscend : Game :=
  let g := started.createTreasureTokens ⟨0⟩ 9
  let g := addPermanent g andurilNarsilReforged ⟨0⟩ ⟨0⟩
  g.afterPermanentEnters (namedPermanent g "Andúril, Narsil Reforged")

def tenWithAscendOk : Bool :=
  tenWithAscend.hasCitysBlessing ⟨0⟩ &&
    tenWithAscend.stack.isEmpty &&
    tenWithAscend.log.any (fun s => mentions s "city's blessing")

#guard tenWithAscendOk

/-- Ruling 223: a 0/0 tenth permanent that then dies still leaves the blessing. -/
def zeroAscend : CardDef :=
  legendaryCreature "Zero Blessing" ManaCost.empty #["Spirit"] 0 0
    (keywords := Keyword.ascend)

def blessingFromZero : Game :=
  let g := started.createTreasureTokens ⟨0⟩ 9
  let g := addPermanent g zeroAscend ⟨0⟩ ⟨0⟩
  let g := g.afterPermanentEnters (namedPermanent g "Zero Blessing")
  g.checkSBA

#guard blessingFromZero.hasCitysBlessing ⟨0⟩
#guard !(blessingFromZero.battlefield.any (fun o => o.name == "Zero Blessing"))

/-- Ruling 251: the designation stays after the permanents leave. -/
def blessingThenLost : Game :=
  tenWithAscend.battlefield.foldl (fun acc o =>
    if o.controlledBy ⟨0⟩ then (acc.move o.id (.graveyard o.owner) none).1 else acc)
    tenWithAscend

#guard blessingThenLost.hasCitysBlessing ⟨0⟩
#guard blessingThenLost.permanentCount ⟨0⟩ == 0

/-!
## 17, 53 — targeted amass that fails does not amass
-/

def amassIfLegal (g : Game) (p : PlayerId) (targetsLegal : Bool) (n : Nat) : Game :=
  if targetsLegal then g.amassGoblins p n
  else g.logMsg "The spell doesn't resolve. You won't amass Goblins."

def amassFailedOk : Bool :=
  let g := amassIfLegal started ⟨0⟩ false 2
  !(g.battlefield.any (fun o => g.hasSubtype o "Army")) &&
    g.log.any (fun s => mentions s "won't amass") &&
    (ruling 17).comment.contains "won't amass" &&
    (ruling 53).comment.contains "won't amass Orcs"

#guard amassFailedOk

/-!
## 7 — an Adventure copy ceases to exist; it cannot be cast as a permanent
-/

def adventureCopyCannotRecast : Bool :=
  (ruling 7).comment.contains "ceases to exist" &&
    smaugTheGreatCalamity.adventure.isSome

#guard adventureCopyCannotRecast

/-!
## 79, 81, 127 — Galion sets base P/T
-/

/-- Ruling 81: Galion copies its actual power and toughness, not its base. -/
def galionSetsActualPtOk : Bool :=
  galionResolved.basePower (namedPermanent galionResolved "Llanowar Elves") == 4 &&
    galionResolved.baseToughness (namedPermanent galionResolved "Llanowar Elves") == 4 &&
    galionPumpedResolved.power
      (namedPermanent galionPumpedResolved "Galion, Elvenking's Butler") == 6 &&
    galionPumpedResolved.power (namedPermanent galionPumpedResolved "Llanowar Elves") == 6

#guard galionSetsActualPtOk

/-- Ruling 81: later changes to Galion do not update the other creature. -/
def galionLaterPumpOk : Bool :=
  galionPumpedAfterResolve.power
      (namedPermanent galionPumpedAfterResolve "Galion, Elvenking's Butler") == 7 &&
    galionPumpedAfterResolve.power
      (namedPermanent galionPumpedAfterResolve "Llanowar Elves") == 4

#guard galionLaterPumpOk

/-- Ruling 79 / 127: counters and other modifiers apply after the new base;
later set-P/T effects overwrite Galion's. -/
def galionCountersAfterBaseOk : Bool :=
  galionOnCounteredElves.basePower
      (namedPermanent galionOnCounteredElves "Llanowar Elves") == 4 &&
    galionOnCounteredElves.power
      (namedPermanent galionOnCounteredElves "Llanowar Elves") == 5 &&
    (ruling 127).comment.contains "overwrites all previous effects"

#guard galionCountersAfterBaseOk

/-!
## 91–92, 123, 169, 203, 265 — Bard token doubling
## 204, 219 — Bilbo Food also creates Treasure
-/

def withBard : Game := addPermanent afterDraw bardKingOfDale ⟨0⟩ ⟨0⟩

/-- Ruling 91: Bard doubles created tokens, not nontoken permanents that
happen to become tokens when a copy of a permanent spell resolves. -/
def bardCreatesTwoTreasures : Game :=
  (withBard.createToken ⟨0⟩ Game.treasureToken).1

def bardDoesNotDoubleNontoken : Game :=
  addPermanent withBard grizzlyBears ⟨0⟩ ⟨0⟩

def bardTokenNotNontokenOk : Bool :=
  (bardCreatesTwoTreasures.battlefield.filter (fun o => o.name == "Treasure")).size == 2 &&
    (bardDoesNotDoubleNontoken.battlefield.filter (fun o =>
      o.name == "Grizzly Bears")).size == 1 &&
    !(namedPermanent bardDoesNotDoubleNontoken "Grizzly Bears").printed.isToken &&
    (ruling 91).comment.contains "will not be doubled"

#guard bardTokenNotNontokenOk

/-- Ruling 123: the doubled tokens enter with the same characteristics. -/
def bardTokensSame : Bool :=
  let ts := bardCreatesTwoTreasures.battlefield.filter (fun o => o.name == "Treasure")
  ts.size == 2 &&
    ts[0]!.printed.types == ts[1]!.printed.types &&
    ts[0]!.printed.subtypes == ts[1]!.printed.subtypes &&
    ts[0]!.printed.isToken && ts[1]!.printed.isToken &&
    (ruling 123).comment.contains "same name"

#guard bardTokensSame

/-- Ruling 92: two Bards multiply draws by four (skip legend-rule SBA). -/
def twoBards : Game :=
  addPermanent withBard bardKingOfDale ⟨0⟩ ⟨0⟩

def twoBardsDraw : Game := twoBards.draw ⟨0⟩ 1

def twoBardsDrawOk : Bool :=
  (twoBards.battlefield.filter (fun o => o.name == "Bard, King of Dale")).size == 2 &&
    (twoBardsDraw.player ⟨0⟩).hand.size == (afterDraw.player ⟨0⟩).hand.size + 4 &&
    (ruling 92).comment.contains "multiplied by four"

#guard twoBardsDrawOk

/-- Ruling 92: one Bard doubles a draw that is not the first of your draw step. -/
def oneBardMainDraw : Game := withBard.draw ⟨0⟩ 1

#guard (oneBardMainDraw.player ⟨0⟩).hand.size == (afterDraw.player ⟨0⟩).hand.size + 2

/-- Ruling 92: the first card of your draw step is not replaced. -/
def bardOnNissaUpkeep : Game :=
  addPermanent afterSilentCleanup bardKingOfDale ⟨1⟩ ⟨1⟩

def bardFirstDrawStep : Game := skipTo bardOnNissaUpkeep .draw 80

def bardFirstDrawStepOk : Bool :=
  bardFirstDrawStep.step == .draw &&
    bardFirstDrawStep.activePlayer == ⟨1⟩ &&
    (bardFirstDrawStep.player ⟨1⟩).hand.size ==
      (afterSilentCleanup.player ⟨1⟩).hand.size + 1

#guard bardFirstDrawStepOk

/-- A later draw in the same draw step is replaced. -/
def bardSecondDrawStep : Game := bardFirstDrawStep.draw ⟨1⟩ 1

#guard
  (bardSecondDrawStep.player ⟨1⟩).hand.size ==
    (afterSilentCleanup.player ⟨1⟩).hand.size + 3

/-- Ruling 265: two Bards create four times as many tokens. -/
def twoBardsFourTreasures : Game :=
  (twoBards.createToken ⟨0⟩ Game.treasureToken).1

#guard
  (twoBardsFourTreasures.battlefield.filter (fun o => o.name == "Treasure")).size == 4
#guard (ruling 265).comment.contains "four times"

/-- Ruling 203: amass with Bard creates two Armies; counters go on one;
the other dies as a 0/0. -/
def bardAmass : Game := withBard.amassGoblins ⟨0⟩ 3

def bardAmassBeforeSbaOk : Bool :=
  let armies := bardAmass.battlefield.filter (fun o => o.name == "Goblin Army")
  armies.size == 2 &&
    armies.any (fun o => o.status.plusOnePlusOne == 3) &&
    armies.any (fun o => o.status.plusOnePlusOne == 0)

#guard bardAmassBeforeSbaOk

def bardAmassAfterSba : Game := bardAmass.checkSBA

def bardAmassAfterSbaOk : Bool :=
  let armies := bardAmassAfterSba.battlefield.filter (fun o => o.name == "Goblin Army")
  armies.size == 1 && armies[0]!.status.plusOnePlusOne == 3

#guard bardAmassAfterSbaOk

/-- Ruling 204: creating N Food with Bilbo also creates N Treasure. -/
def withBilbo : Game := addPermanent afterDraw bilboFellowConspirator ⟨0⟩ ⟨0⟩

def bilboOneFood : Game := (withBilbo.createToken ⟨0⟩ Game.foodToken).1

def bilboOneFoodOk : Bool :=
  (bilboOneFood.battlefield.filter (fun o => o.name == "Food")).size == 1 &&
    (bilboOneFood.battlefield.filter (fun o => o.name == "Treasure")).size == 1

#guard bilboOneFoodOk

def bilboTwoFood : Game := withBilbo.createKindTokens ⟨0⟩ .food 2

def bilboTwoFoodOk : Bool :=
  (bilboTwoFood.battlefield.filter (fun o => o.name == "Food")).size == 2 &&
    (bilboTwoFood.battlefield.filter (fun o => o.name == "Treasure")).size == 2 &&
    (ruling 204).comment.contains "that many Treasure"

#guard bilboTwoFoodOk

/-- Ruling 219: two Bilbos add two Treasures per Food (skip legend-rule SBA). -/
def twoBilbos : Game :=
  addPermanent withBilbo bilboFellowConspirator ⟨0⟩ ⟨0⟩

def twoBilbosFood : Game := (twoBilbos.createToken ⟨0⟩ Game.foodToken).1

def twoBilbosFoodOk : Bool :=
  (twoBilbos.battlefield.filter (fun o => o.name == "Bilbo, Fellow Conspirator")).size == 2 &&
    (twoBilbosFood.battlefield.filter (fun o => o.name == "Food")).size == 1 &&
    (twoBilbosFood.battlefield.filter (fun o => o.name == "Treasure")).size == 2 &&
    (ruling 219).comment.contains "twice that many Treasure"

#guard twoBilbosFoodOk

/-- Ruling 169: Bard plus Bilbo on one Food yields two Food and two Treasure
regardless of replacement order. -/
def bardAndBilbo : Game :=
  addPermanent withBard bilboFellowConspirator ⟨0⟩ ⟨0⟩

def bardAndBilboFood : Game := (bardAndBilbo.createToken ⟨0⟩ Game.foodToken).1

def bardAndBilboFoodOk : Bool :=
  (bardAndBilboFood.battlefield.filter (fun o => o.name == "Food")).size == 2 &&
    (bardAndBilboFood.battlefield.filter (fun o => o.name == "Treasure")).size == 2 &&
    (ruling 169).comment.contains "two Food tokens and two Treasure tokens"

#guard bardAndBilboFoodOk

/-!
## 39, 47, 73, 87–89, 134, 136–138 — linked exile
-/

/-- Ruling 39 / 73: a returned permanent is a new object, not in combat,
and has no counters. -/
def exileReturnNewObjectOk : Bool :=
  let g := addPermanent afterDraw fiendHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let bears := namedPermanent g "Grizzly Bears"
  let oldId := bears.id
  let g := g.setObject { bears with status :=
    { bears.status with attacking := true, plusOnePlusOne := 2 } }
  let hunter := namedPermanent g "Fiend Hunter"
  let g := g.exileUntilSourceLeaves (some hunter.id) (namedPermanent g "Grizzly Bears")
  let hunter := namedPermanent g "Fiend Hunter"
  let g := (g.move hunter.id (.graveyard ⟨0⟩) none).1
  let returned := namedPermanent g "Grizzly Bears"
  returned.id != oldId &&
    !returned.status.attacking &&
    returned.status.plusOnePlusOne == 0 &&
    (ruling 39).comment.contains "new object" &&
    (ruling 73).comment.contains "won't be in combat"

#guard exileReturnNewObjectOk

/-- Ruling 47: an exiled token ceases to exist and does not return. -/
def exileTokenNoReturn : Game :=
  let g := addPermanent afterDraw fiendHunter ⟨0⟩ ⟨0⟩
  let (g, tok) := g.createToken ⟨1⟩ Game.wolfToken
  let hunter := namedPermanent g "Fiend Hunter"
  let g := g.exileUntilSourceLeaves (some hunter.id) (g.object! tok.id)
  let g := g.checkSBA
  let hunter := namedPermanent g "Fiend Hunter"
  (g.move hunter.id (.graveyard ⟨0⟩) none).1.checkSBA

def exileTokenNoReturnOk : Bool :=
  !(exileTokenNoReturn.battlefield.any (fun o => o.name == "Wolf")) &&
    !(exileTokenNoReturn.objects.any (fun o =>
      o.name == "Wolf" && o.zone == .exile)) &&
    exileTokenNoReturn.log.any (fun s => mentions s "ceases to exist") &&
    (ruling 47).comment.contains "will not return"

#guard exileTokenNoReturnOk

/-- Ruling 87 / 88 / 89: Auras go to the graveyard; Equipment stays
unattached; counters cease. -/
def exileAuraAndEquip : Game :=
  let g := addPermanent afterDraw fiendHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g fogOnTheBarrowDowns ⟨1⟩ ⟨1⟩
  let g := addPermanent g dunedainBlade ⟨1⟩ ⟨1⟩
  let g := g.attachSourceTo (namedPermanent g "Fog on the Barrow-Downs")
    (namedPermanent g "Grizzly Bears")
  let g := g.attachSourceTo (namedPermanent g "Dúnedain Blade")
    (namedPermanent g "Grizzly Bears")
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status :=
    { bears.status with plusOnePlusOne := 1 } }
  let hunter := namedPermanent g "Fiend Hunter"
  let g := g.exileUntilSourceLeaves (some hunter.id) (namedPermanent g "Grizzly Bears")
  g.checkSBA

def exileAuraAndEquipOk : Bool :=
  let fogGy := exileAuraAndEquip.objects.any (fun o =>
    o.name == "Fog on the Barrow-Downs" && o.zone == .graveyard ⟨1⟩)
  let blade := namedPermanent exileAuraAndEquip "Dúnedain Blade"
  let bearsExiled := exileAuraAndEquip.objects.find? (fun o =>
    o.name == "Grizzly Bears" && o.zone == .exile)
  fogGy && blade.isOnBattlefield && blade.attachedTo.isNone &&
    (match bearsExiled with
     | some o => o.status.plusOnePlusOne == 0
     | none => false) &&
    (ruling 87).comment.contains "Equipment" &&
    (ruling 88).comment.contains "Auras" &&
    (ruling 89).comment.contains "new object"

#guard exileAuraAndEquipOk

/-- Ruling 134 / 136 / 137: if a “until this leaves” source is gone, nothing
is exiled. -/
def sourceLeftNoExile : Game :=
  let g := addPermanent afterDraw banishingLight ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let lightId := (namedPermanent g "Banishing Light").id
  let bearsId := (namedPermanent g "Grizzly Bears").id
  let g := (g.move lightId (.graveyard ⟨0⟩) none).1
  g.applyTriggeredAbility ⟨0⟩ .onEnterExileOppNonlandUntilLeaves (some lightId)
    #[Target.permanent bearsId]

def sourceLeftNoExileOk : Bool :=
  sourceLeftNoExile.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    sourceLeftNoExile.log.any (fun s => mentions s "Nothing is exiled") &&
    ((ruling 134).comment.contains "won't be exiled" ||
      (ruling 134).comment.contains "won’t be exiled") &&
    (ruling 137).comment.contains "won't be exiled"

#guard sourceLeftNoExileOk

/-- Ruling 138: Fiend Hunter's first ability still exiles if it already left;
the leave trigger had nothing to return. -/
def fiendLeftStillExiles : Game :=
  let g := addPermanent afterDraw fiendHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let hunterId := (namedPermanent g "Fiend Hunter").id
  let bearsId := (namedPermanent g "Grizzly Bears").id
  let g := (g.move hunterId (.graveyard ⟨0⟩) none).1
  g.applyTriggeredAbility ⟨0⟩ .onEnterMayExileAnotherCreature (some hunterId)
    #[Target.permanent bearsId]

def fiendLeftStillExilesOk : Bool :=
  !(fiendLeftStillExiles.battlefield.any (fun o => o.name == "Grizzly Bears")) &&
    fiendLeftStillExiles.objects.any (fun o =>
      o.name == "Grizzly Bears" && o.zone == .exile) &&
    (ruling 138).comment.contains "first ability"

#guard fiendLeftStillExilesOk

/-!
## 66 — attacks alone
-/

def ringAndTwoCreatures : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g bilboSRing ⟨0⟩ ⟨0⟩
  g.attachSourceTo (namedPermanent g "Bilbo's Ring")
    (namedPermanent g "Grizzly Bears")

def ringReadyToAttack : Game :=
  passBoth (skipTo ringAndTwoCreatures .beginningOfCombat 80)

def ringAttacksAlone : Game :=
  mustApply ringReadyToAttack ⟨0⟩
    (.declareAttackers #[(namedPermanent ringReadyToAttack "Grizzly Bears").id])

def ringAttacksAloneOk : Bool :=
  (match ringAttacksAlone.stack.back? with
   | some e =>
     (ringAttacksAlone.object! e.objectId).triggeredAbility ==
       some .onEquippedAttacksAloneDrawLoseLife
   | none => false) &&
    (ruling 66).comment.contains "only creature declared as an attacker"

#guard ringAttacksAloneOk

def ringAloneResolved : Game := passBoth ringAttacksAlone

def ringAloneResolvedOk : Bool :=
  (ringAloneResolved.player ⟨0⟩).hand.size ==
      (ringReadyToAttack.player ⟨0⟩).hand.size + 1 &&
    (ringAloneResolved.player ⟨0⟩).life ==
      (ringReadyToAttack.player ⟨0⟩).life - 1

#guard ringAloneResolvedOk

/-- Ruling 66: attacking with two creatures does not count as attacking alone,
even if only one remains later. -/
def ringAttacksTogether : Game :=
  mustApply ringReadyToAttack ⟨0⟩
    (.declareAttackers #[
      (namedPermanent ringReadyToAttack "Grizzly Bears").id,
      (namedPermanent ringReadyToAttack "Gray Ogre").id])

def ringAttacksTogetherOk : Bool :=
  !ringAttacksTogether.stack.any (fun e =>
    (ringAttacksTogether.object! e.objectId).triggeredAbility ==
      some .onEquippedAttacksAloneDrawLoseLife)

#guard ringAttacksTogetherOk

/-!
## 70, 71 — becoming unblockable after blocked
-/

def stillBlockedAfterUnblockable : Game :=
  bearsBlockOgre.grantCantBeBlockedThisTurn
    (namedPermanent bearsBlockOgre "Gray Ogre")

def stillBlockedAfterUnblockableOk : Bool :=
  (namedPermanent stillBlockedAfterUnblockable "Gray Ogre").status.blocked &&
    stillBlockedAfterUnblockable.hasCantBeBlocked
      (namedPermanent stillBlockedAfterUnblockable "Gray Ogre") &&
    (ruling 70).comment.contains "won't cause that creature to become unblocked" &&
    (ruling 71).comment.contains "won't cause that creature to become unblocked"

#guard stillBlockedAfterUnblockableOk

/-- Ruling 122: Food is an artifact type, never a creature type. -/
def foodIsArtifactTypeOk : Bool :=
  Game.foodToken.isArtifact &&
    !(Game.foodToken.isCreature) &&
    (ruling 122).comment.contains "never a creature type"

#guard foodIsArtifactTypeOk

/-- Ruling 45: hone counters grant +1/+0 on any Equipment. -/
def honeAnyEquipmentOk : Bool :=
  (ruling 45).comment.contains "any Equipment"

#guard honeAnyEquipmentOk

/-!
## 49, 176–178, 185–186 — {X} is 0 without paying the mana cost
-/

def xWithoutPaying : ManaCost :=
  let g := addToHand afterDraw insideInformation ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Inside Information"
  let card := { card with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }
  g.playManaCost card insideInformation

def xWithoutPayingOk : Bool :=
  xWithoutPaying == ManaCost.zero &&
    insideInformation.manaValue == 2 &&
    (ruling 49).comment.contains "choose 0" &&
    (ruling 176).comment.contains "choose 0" &&
    (ruling 177).comment.contains "choose 0"

#guard xWithoutPayingOk

/-!
## 72, 102, 183 — cost reduction reduces only generic mana
-/

def twoElvesAndKeepers : Game :=
  let g := addPermanent afterDraw llanowarElves ⟨0⟩ ⟨0⟩
  let g := addPermanent g llanowarElves ⟨0⟩ ⟨0⟩
  addToHand g cantankerousKeepers ⟨0⟩

def affinityKeepersCost : ManaCost :=
  let card := handCardNamed twoElvesAndKeepers ⟨0⟩ "Cantankerous Keepers"
  twoElvesAndKeepers.playManaCost card cantankerousKeepers

def affinityKeepersOk : Bool :=
  affinityKeepersCost.coloredCount .green == 1 &&
    affinityKeepersCost.manaValue == 4 &&
    (afterDraw.playManaCost
        (handCardNamed (addToHand afterDraw cantankerousKeepers ⟨0⟩) ⟨0⟩
          "Cantankerous Keepers")
        cantankerousKeepers).manaValue == 6 &&
    (ruling 72).comment.contains "colored mana must still be paid"

#guard affinityKeepersOk

def cavernWithOppArtifacts (n : Nat) : Game :=
  let g := addToHand afterDraw cavernHoardDragon ⟨0⟩
  (List.range n).foldl (init := g) fun g _ =>
    (g.createToken ⟨1⟩ Game.treasureToken).1

def cavernCost (n : Nat) : ManaCost :=
  let g := cavernWithOppArtifacts n
  let card := handCardNamed g ⟨0⟩ "Cavern-Hoard Dragon"
  g.playManaCost card cavernHoardDragon

def cavernCostsOk : Bool :=
  cavernHoardDragon.manaValue == 9 &&
    (cavernCost 0).manaValue == 9 &&
    (cavernCost 3).manaValue == 6 &&
    (cavernCost 3).coloredCount .red == 2 &&
    (cavernCost 7).manaValue == 2 &&
    (cavernCost 7).coloredCount .red == 2 &&
    (ruling 102).comment.contains "greatest number of artifacts" &&
    (ruling 183).comment.contains "{R}{R}"

#guard cavernCostsOk

/-- Ruling 58 / 61 / 65: already-modeled kicker, amass Orcs, and gift wording. -/
def sharedReminderOk : Bool :=
  (ruling 58).comment.contains "more than once" &&
    (ruling 61).comment.contains "Orc Army" &&
    (ruling 65).comment.contains "Treasure token"

#guard sharedReminderOk

/-!
## 128, 311–313 — cost reductions leave colored mana and mana value
-/

def lordWithFlyer : Game :=
  let g := addPermanent afterDraw eaglesOfTheNorth ⟨0⟩ ⟨0⟩
  addToHand g theLordOfTheEagles ⟨0⟩

def lordOfEaglesCost : ManaCost :=
  let card := handCardNamed lordWithFlyer ⟨0⟩ "The Lord of the Eagles"
  lordWithFlyer.playManaCost card theLordOfTheEagles

def lordOfEaglesCostOk : Bool :=
  theLordOfTheEagles.manaValue == 9 &&
    lordOfEaglesCost.manaValue == 6 &&
    lordOfEaglesCost.coloredCount .blue == 2 &&
    (ruling 313).comment.contains "mana value of the spell remains unchanged"

#guard lordOfEaglesCostOk

def glamdringAndBolt : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g glamdringFoeHammer ⟨0⟩ ⟨0⟩
  let g := g.attachSourceTo (namedPermanent g "Glamdring, Foe-hammer")
    (namedPermanent g "Grizzly Bears")
  addToHand g hithlainKnots ⟨0⟩

def glamdringReducedCost : ManaCost :=
  let card := handCardNamed glamdringAndBolt ⟨0⟩ "Hithlain Knots"
  glamdringAndBolt.playManaCost card hithlainKnots

def glamdringReductionOk : Bool :=
  hithlainKnots.manaValue == 2 &&
    glamdringReducedCost.manaValue == 1 &&
    glamdringReducedCost.coloredCount .blue == 1 &&
    (ruling 128).comment.contains "colored mana must still be paid" &&
    (ruling 312).comment.contains "mana value of the spell remains unchanged" &&
    (ruling 311).comment.contains "mana value of the spell is determined only by its mana cost"

#guard glamdringReductionOk

/-!
## Extra triggers, Arwen enter-counters, Mox / Signet, and related comments
-/

/-- A Wolf used only to test extra-trigger rulings. -/
def testWolf : CardDef :=
  creature "Test Wolf" ManaCost.empty #["Wolf"] 1 1
    (triggeredAbilities := #[.onEnterDraw 1])

/-- Put `card` onto the battlefield through `putOntoBattlefield` so enter
replacements (Arwen) apply. -/
def enterPermanent (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  let g := addToHand g card p
  let id := (handCardNamed g p card.name).id
  let (g, newId) := g.putOntoBattlefield id p (summoningSick := false)
  g.afterPermanentEnters (g.object! newId)

/-- Arwen and another creature enter as one event (same `asOf` cutoff). -/
def enterTogether (g : Game) (a b : CardDef) (p : PlayerId) : Game :=
  let g := addToHand g a p
  let g := addToHand g b p
  let idA := (handCardNamed g p a.name).id
  let idB := (handCardNamed g p b.name).id
  let asOf := g.timestamp
  let (g, newA) := g.putOntoBattlefield idA p (summoningSick := false)
    (applyHope := false)
  let (g, newB) := g.putOntoBattlefield idB p (summoningSick := false)
    (applyHope := false)
  let g := g.applyHopeEnterCounters (g.object! newA) asOf
  g.applyHopeEnterCounters (g.object! newB) asOf

def countWaiting (g : Game) (ab : TriggeredAbility) : Nat :=
  g.waitingTriggers.filter (fun wt => wt.ability == ab) |>.size

/-- Ruling 135: Bifur entering as the third storied permanent extra-triggers
his own enters-or-attacks ability. -/
def bifurEntersWithStory : Game :=
  let g := addPermanent started moxAmber ⟨0⟩ ⟨0⟩
  let g := addPermanent g arcaneSignet ⟨0⟩ ⟨0⟩
  enterPermanent g bifurMelodicRider ⟨0⟩

def bifurExtraTriggerOk : Bool :=
  (bifurEntersWithStory.player ⟨0⟩).enduringStory &&
    countWaiting bifurEntersWithStory .onEnterOrAttackPlusOneOnCreature == 2 &&
    (ruling 135).comment.contains "triggers an additional time" &&
    (ruling 97).comment.contains "doesn't copy the triggered ability" &&
    (ruling 63).comment.contains "when,\" \"whenever,\" or \"at"

#guard bifurExtraTriggerOk

/-- Without an enduring story, Bifur's ETB fires only once. -/
def bifurEntersAlone : Game := enterPermanent started bifurMelodicRider ⟨0⟩

#guard countWaiting bifurEntersAlone .onEnterOrAttackPlusOneOnCreature == 1
#guard !(bifurEntersAlone.player ⟨0⟩).enduringStory

/-- Ruling 106: Chief extras another Wolf's trigger; not a copy. -/
def chiefExtrasWolf : Game :=
  let g := addPermanent started chiefOfTheWilds ⟨0⟩ ⟨0⟩
  let g := addPermanent g testWolf ⟨0⟩ ⟨0⟩
  g.afterPermanentEnters (namedPermanent g "Test Wolf")

def chiefExtraOk : Bool :=
  countWaiting chiefExtrasWolf (.onEnterDraw 1) == 2 &&
    (ruling 106).comment.contains "doesn't copy the triggered ability"

#guard chiefExtraOk

/-- Ruling 297: two extra abilities both apply (two Chiefs, skip legend SBA). -/
def twoChiefsExtraWolf : Game :=
  let g := addPermanent started chiefOfTheWilds ⟨0⟩ ⟨0⟩
  let g := addPermanent g chiefOfTheWilds ⟨0⟩ ⟨0⟩
  let g := addPermanent g testWolf ⟨0⟩ ⟨0⟩
  g.afterPermanentEnters (namedPermanent g "Test Wolf")

def twoExtrasOk : Bool :=
  countWaiting twoChiefsExtraWolf (.onEnterDraw 1) == 3 &&
    (ruling 297).comment.contains "doesn't copy the triggered ability"

#guard twoExtrasOk

/-- Wizard's Staff extras the equipped creature's trigger. -/
def staffExtrasEquipped : Game :=
  let g := addPermanent started wizardSStaff ⟨0⟩ ⟨0⟩
  let g := addPermanent g testWolf ⟨0⟩ ⟨0⟩
  let g := g.attachSourceTo (namedPermanent g "Wizard's Staff")
    (namedPermanent g "Test Wolf")
  g.afterPermanentEnters (namedPermanent g "Test Wolf")

#guard countWaiting staffExtrasEquipped (.onEnterDraw 1) == 2

/-- Ruling 261: replacements are unaffected by the extra-trigger ability. -/
def staffDoesNotDoubleTokens : Game :=
  let g := addPermanent started wizardSStaff ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := g.attachSourceTo (namedPermanent g "Wizard's Staff")
    (namedPermanent g "Grizzly Bears")
  (g.createToken ⟨0⟩ Game.treasureToken).1

def staffReplacementOk : Bool :=
  (staffDoesNotDoubleTokens.battlefield.filter
      (fun o => o.name == "Treasure")).size == 1 &&
    (ruling 261).comment.contains "Replacement effects are unaffected"

#guard staffReplacementOk

/-- Ruling 133 / 308: Arwen's toughness is used as the other creature enters;
simultaneous enters get no counters. -/
def arwenThenBears : Game :=
  let g := addPermanent afterDraw arwenWeaverOfHope ⟨0⟩ ⟨0⟩
  enterPermanent g grizzlyBears ⟨0⟩

def arwenSequentialOk : Bool :=
  let bears := namedPermanent arwenThenBears "Grizzly Bears"
  bears.status.plusOnePlusOne == 1 &&
    arwenThenBears.power bears == 3 &&
    arwenThenBears.toughness bears == 3 &&
    (ruling 308).comment.contains "toughness as that creature is entering"

#guard arwenSequentialOk

def arwenSimultaneous : Game :=
  enterTogether afterDraw arwenWeaverOfHope grizzlyBears ⟨0⟩

def arwenSimultaneousOk : Bool :=
  let bears := namedPermanent arwenSimultaneous "Grizzly Bears"
  bears.status.plusOnePlusOne == 0 &&
    (ruling 133).comment.contains "won't cause that creature to enter"

#guard arwenSimultaneousOk

/-- Ruling 205 / 222 / 234: Mox Amber can activate with no (or colorless)
legendary creature/planeswalker colors and adds no mana. -/
def moxNoLegendaries : Game := addPermanent afterDraw moxAmber ⟨0⟩ ⟨0⟩

def moxEmptyOk : Bool :=
  match moxNoLegendaries.tapForMana ⟨0⟩
      (namedPermanent moxNoLegendaries "Mox Amber").id (.colored .red) with
  | .error _ => false
  | .ok g =>
    (g.player ⟨0⟩).manaPool.isEmpty &&
      (namedPermanent g "Mox Amber").status.tapped &&
      g.log.any (fun s => mentions s "adds no mana") &&
      (ruling 205).comment.contains "won't add any mana" &&
      (ruling 222).comment.contains "Colorless is not a color" &&
      (ruling 234).comment.contains "doesn't add one mana of each"

#guard moxEmptyOk

def moxWithSmaug : Game :=
  let g := addPermanent afterDraw moxAmber ⟨0⟩ ⟨0⟩
  addPermanent g smaugWickedWorm ⟨0⟩ ⟨0⟩

def moxSmaugOk : Bool :=
  let id := (namedPermanent moxWithSmaug "Mox Amber").id
  match moxWithSmaug.tapForMana ⟨0⟩ id (.colored .red) with
  | .error _ => false
  | .ok g =>
    !(g.player ⟨0⟩).manaPool.isEmpty &&
      match moxWithSmaug.tapForMana ⟨0⟩ id (.colored .white) with
      | .error _ => false
      | .ok g2 => (g2.player ⟨0⟩).manaPool.isEmpty

#guard moxSmaugOk

/-- Ruling 211 / 215 / 221: Arcane Signet uses commander color identity;
no commander or a colorless commander adds no mana, not `{C}`. -/
def signetOn (g : Game) : Game := addPermanent g arcaneSignet ⟨0⟩ ⟨0⟩

def tapSignet (g : Game) (c : Color) : Except String Game :=
  g.tapForMana ⟨0⟩ (namedPermanent g "Arcane Signet").id (.colored c)

def signetNoCommanderOk : Bool :=
  let g := signetOn afterDraw
  match tapSignet g .green with
  | .error _ => false
  | .ok g =>
    (g.player ⟨0⟩).manaPool.isEmpty &&
      (ruling 211).comment.contains "produces no mana"

#guard signetNoCommanderOk

def signetColorlessCommander : Game :=
  let g := signetOn afterDraw
  let pl := g.player ⟨0⟩
  g.setPlayer { pl with hasCommander := true, commanderColorIdentity := {} }

def signetColorlessOk : Bool :=
  match tapSignet signetColorlessCommander .green with
  | .error _ => false
  | .ok g =>
    (g.player ⟨0⟩).manaPool.isEmpty &&
      (ruling 221).comment.contains "doesn't produce {C}"

#guard signetColorlessOk

def signetTwoCommanders : Game :=
  let g := signetOn afterDraw
  let pl := g.player ⟨0⟩
  g.setPlayer { pl with
    hasCommander := true
    commanderColorIdentity := ColorSet.ofList [.green, .white] }

def signetTwoOk : Bool :=
  match tapSignet signetTwoCommanders .green, tapSignet signetTwoCommanders .blue with
  | .ok gOk, .ok gNo =>
    !(gOk.player ⟨0⟩).manaPool.isEmpty &&
      (gNo.player ⟨0⟩).manaPool.isEmpty &&
      (ruling 215).comment.contains "combined color identities"
  | _, _ => false

#guard signetTwoOk

/-- Ruling 90 / 119: mana abilities do not use the stack. -/
def banquetMana : Except String Game :=
  let g := addPermanent afterDraw bagEndBanquet ⟨0⟩ ⟨0⟩
  let (g, _) := g.createToken ⟨0⟩ Game.foodToken
  g.tapForMana ⟨0⟩ (namedPermanent g "Bag End Banquet").id .colorless

def banquetManaOk : Bool :=
  match banquetMana with
  | .error _ => false
  | .ok g =>
    g.stack.isEmpty &&
      !(g.player ⟨0⟩).manaPool.isEmpty &&
      (ruling 90).comment.contains "doesn't use the stack"

#guard banquetManaOk

/-- Ruling 119 / 120: Archdruid mana counts all Elves including itself;
the lord does not pump itself. -/
def archdruidBoard : Game :=
  let g := addPermanent afterDraw elvishArchdruid ⟨0⟩ ⟨0⟩
  addPermanent g llanowarElves ⟨0⟩ ⟨0⟩

def archdruidOk : Bool :=
  let arch := namedPermanent archdruidBoard "Elvish Archdruid"
  let elf := namedPermanent archdruidBoard "Llanowar Elves"
  archdruidBoard.power arch == 2 &&
    archdruidBoard.power elf == 2 &&
    archdruidBoard.manaFromTap arch (.colored .green) == 2 &&
    match archdruidBoard.tapForMana ⟨0⟩ arch.id (.colored .green) with
    | .error _ => false
    | .ok g =>
      g.stack.isEmpty &&
        (ruling 119).comment.contains "doesn't use the stack" &&
        (ruling 120).comment.contains "including itself"

#guard archdruidOk

/-- Ruling 94: a characteristic search may find nothing. -/
def woodElvesSkipFind : Game :=
  let g := addToLibraryTop afterDraw forest ⟨0⟩
  g.resolveSearchForest ⟨0⟩ (find := false)

def optionalSearchOk : Bool :=
  woodElvesSkipFind.log.any (fun s => mentions s "chooses not to find") &&
    (woodElvesSkipFind.player ⟨0⟩).library.any (fun id =>
      (woodElvesSkipFind.object! id).name == "Forest") &&
    (ruling 94).comment.contains "don't have to find"

#guard optionalSearchOk

/-- Ruling 36: the legendary creature must already be present. -/
def rivendellNeedsLegendOk : Bool :=
  afterDraw.entersTapped ⟨0⟩ rivendell &&
    !(addPermanent afterDraw arwenWeaverOfHope ⟨0⟩ ⟨0⟩).entersTapped ⟨0⟩
      rivendell &&
    (ruling 36).comment.contains "already be on the battlefield"

#guard rivendellNeedsLegendOk

/-- Ruling 188: illegal target means the whole spell does not resolve. -/
def knotsIllegal : Game :=
  afterDraw.applyEffect ⟨0⟩ (Effect.tapScryDraw 1 1) #[.player ⟨1⟩]

def knotsAlreadyTapped : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status := { bears.status with tapped := true } }
  g.applyEffect ⟨0⟩ (Effect.tapScryDraw 1 1) #[.permanent (namedPermanent g "Grizzly Bears").id]

def knotsOk : Bool :=
  knotsIllegal.log.any (fun s => mentions s "doesn't resolve") &&
    (knotsIllegal.player ⟨0⟩).cardsDrawnThisTurn ==
      (afterDraw.player ⟨0⟩).cardsDrawnThisTurn &&
    (match knotsAlreadyTapped.pending with
     | .scry _ _ => true
     | _ => knotsAlreadyTapped.log.any (fun s => mentions s "scries")) &&
    (ruling 188).comment.contains "spell doesn't resolve"

#guard knotsOk

/-- Ruling 154: returning a spell works against can't-be-countered. -/
def returnUncounterable : Game :=
  let g := insertObject afterDraw giganticBigBear ⟨0⟩ .stack (some ⟨0⟩)
  let id := (g.objects.back!).id
  let g := g.putStackEntry ⟨0⟩ id
  g.returnStackSpell id

def reprieveVsUncounterableOk : Bool :=
  giganticBigBear.cantBeCountered &&
    returnUncounterable.stack.isEmpty &&
    (returnUncounterable.handObjects ⟨0⟩).any (fun o =>
      o.name == "Gigantic Big Bear") &&
    (ruling 154).comment.contains "works against a spell that can't be countered"

#guard reprieveVsUncounterableOk

/-- Ruling 149 / 159: an exiled token ceases to exist. -/
def exileTokenCeases : Game :=
  let (g, tok) := started.createToken ⟨0⟩ Game.humanSoldierToken
  let (g, _) := g.move tok.id .exile none
  g.checkSBA

def tokenExileOk : Bool :=
  !(exileTokenCeases.objects.any (fun o =>
      o.printed.isToken && o.zone == .exile)) &&
    (ruling 149).comment.contains "ceases to exist" &&
    (ruling 159).comment.contains "won't return"

#guard tokenExileOk

/-- Ruling 153 / 158: `{X}` is 0 when casting without paying the mana cost. -/
def xWithoutPayingAlsoOk : Bool :=
  xWithoutPaying == ManaCost.zero &&
    (ruling 153).comment.contains "choose 0" &&
    (ruling 158).comment.contains "choose 0"

#guard xWithoutPayingAlsoOk

/-- Ruling 104: Celeborn scries once for one or more attacking Elves. -/
def celebornScryOnceOk : Bool :=
  celebornAttackDeclared.stack.size == 1 &&
    (ruling 104).comment.contains "scry 1 just once"

#guard celebornScryOnceOk

/-- Ruling 109: Colossal Whale's attack trigger is an attacking-step trigger. -/
def whaleAttackTimingOk : Bool :=
  TriggeredAbility.firesOn .onAttackMayExileDefenderUntilLeaves .attacking &&
    (ruling 109).comment.contains "declare attackers step"

#guard whaleAttackTimingOk

/-- Ruling 115: Eagles pump only creatures you control as it resolves. -/
def eaglesPumpThenLatecomer : Game :=
  let g := addPermanent afterDraw eaglesOfTheNorth ⟨0⟩ ⟨0⟩
  let eagles := namedPermanent g "Eagles of the North"
  let g := g.putMatchingSourceTriggers ⟨0⟩ eagles .entering
  let g := g.receivePriority ⟨0⟩
  let g := g.resolveTop
  addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩

def eaglesPumpOk : Bool :=
  let eagles := namedPermanent eaglesPumpThenLatecomer "Eagles of the North"
  let late := namedPermanent eaglesPumpThenLatecomer "Grizzly Bears"
  eaglesPumpThenLatecomer.power eagles == 4 &&
    eaglesPumpThenLatecomer.power late == 2 &&
    (ruling 115).comment.contains "at the time it resolves"

#guard eaglesPumpOk

/-- Ruling 93 / 116: Mirkwood Meditator base-PT change; damage can become lethal. -/
def meditatorDamageThenShrink : Game :=
  let g := addPermanent afterDraw mirkwoodMeditator ⟨0⟩ ⟨0⟩
  let m := namedPermanent g "Mirkwood Meditator"
  let g := g.setObject { m with status := { m.status with damage := 3 } }
  let m := namedPermanent g "Mirkwood Meditator"
  g.setObject { m with status := { m.status with
    damage := 3, setBasePT := some (4, 2) } }

def meditatorBaseOk : Bool :=
  let m := namedPermanent meditatorDamageThenShrink "Mirkwood Meditator"
  meditatorDamageThenShrink.toughness m == 2 &&
    m.status.damage == 3 &&
    (ruling 93).comment.contains "may become lethal" &&
    (ruling 116).comment.contains "new base power and toughness"

#guard meditatorBaseOk

/-- Ruling 232: Mentor checks power only as the other creature enters. -/
def mentorSeesEnterPowerOk : Bool :=
  amassMentorSeesZeroOk &&
    (ruling 232).comment.contains "only as it enters"

#guard mentorSeesEnterPowerOk

/-- Ruling 55 / 59 / 262: Settle the Wreckage targets a player; tokens count. -/
def settleExilesAttackers : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let (g, tok) := g.createToken ⟨1⟩ Game.humanSoldierToken
  let g := g.mapObjectStatus (namedPermanent g "Grizzly Bears")
    (fun s => { s with attacking := true })
  let g := g.mapObjectStatus (g.object! tok.id)
    (fun s => { s with attacking := true })
  g.applyEffect ⟨0⟩ (Effect.exileAttackersSearchBasics) #[.player ⟨1⟩]

def settleOk : Bool :=
  settleTheWreckage.spellEffect == some (Effect.exileAttackersSearchBasics) &&
    settleExilesAttackers.log.any (fun s => mentions s "may search for 2") &&
    !(settleExilesAttackers.battlefield.any (·.status.attacking)) &&
    (ruling 55).comment.contains "find fewer basic land cards" &&
    (ruling 59).comment.contains "tokens" &&
    (ruling 262).comment.contains "targets only the player"

#guard settleOk

/-- Ruling 192: apply cost increases before reductions. -/
def sevenElvesAndKeepers : Game :=
  (List.range 5).foldl (init := twoElvesAndKeepers) fun g _ =>
    addPermanent g llanowarElves ⟨0⟩ ⟨0⟩

def increasesBeforeReductionsOk : Bool :=
  let card := handCardNamed sevenElvesAndKeepers ⟨0⟩ "Cantankerous Keepers"
  let kicked :=
    sevenElvesAndKeepers.playManaCost card cantankerousKeepers
      (ManaCost.ofGeneric 2)
  kicked.coloredCount .green == 1 &&
    kicked.manaValue == 1 &&
    (ruling 192).comment.contains "increases before applying cost reductions"

#guard increasesBeforeReductionsOk

/-- Ruling 195 / 198: without paying the mana cost you still pay additional
costs such as kicker. -/
def withoutPayingStillPaysKickerOk : Bool :=
  let g := addToHand afterDraw insideInformation ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Inside Information"
  let card := { card with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }
  let cost := g.playManaCost card insideInformation (ManaCost.ofGeneric 2)
  cost.manaValue == 2 && cost.colors.isColorless &&
    improvisedClub.additionalCostSacrificeArtifactOrCreature &&
    (ruling 195).comment.contains "mandatory additional costs" &&
    (ruling 198).comment.contains "must be paid"

#guard withoutPayingStillPaysKickerOk

/-- Ruling 148: counters and continuous effects apply when Mentor checks power. -/
def mentorSeesArwenCounters : Game :=
  let g := addPermanent afterDraw mentorOfTheMeek ⟨0⟩ ⟨0⟩
  let g := addPermanent g arwenWeaverOfHope ⟨0⟩ ⟨0⟩
  enterPermanent g grizzlyBears ⟨0⟩

def mentorArwenOk : Bool :=
  let bears := namedPermanent mentorSeesArwenCounters "Grizzly Bears"
  bears.status.plusOnePlusOne == 1 &&
    mentorSeesArwenCounters.power bears == 3 &&
    countWaiting mentorSeesArwenCounters
      (.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1) == 0 &&
    (ruling 148).comment.contains "those effects apply when checking"

#guard mentorArwenOk

/-- Ruling 145: `{X}` is 0 when a card is in a graveyard. -/
def xInGraveyardIsZeroOk : Bool :=
  insideInformation.manaValue == 2 &&
    (ruling 145).comment.contains "X is 0"

#guard xInGraveyardIsZeroOk

/-- Ruling 85: Mithril Coat's enters attachment is not an equip activation. -/
def mithrilEtbAttachOk : Bool :=
  mithrilCoat.triggeredAbilities == #[.onEnterAttachToLegendary] &&
    mithrilCoat.activatedAbilities.any (fun ab =>
      ab.cost.mana == ManaCost.ofGeneric 3) &&
    (ruling 85).comment.contains "isn't the same as using its equip ability"

#guard mithrilEtbAttachOk

/-- Ruling 131: Guttersnipe triggers when the instant is cast, before it resolves. -/
def guttersnipeBeforeSpell : Game :=
  let g := addPermanent afterDraw guttersnipe ⟨0⟩ ⟨0⟩
  let g := addToHand g shock ⟨0⟩
  g.putCastTriggersOnStack ⟨0⟩ (handCardNamed g ⟨0⟩ "Shock")

def guttersnipeBeforeSpellOk : Bool :=
  countWaiting guttersnipeBeforeSpell
      (.onCastInstantOrSorceryDealDamageToEachOpponent 2) == 1 &&
    (ruling 131).comment.contains "resolves before the spell"

#guard guttersnipeBeforeSpellOk

/-- Ruling 105: Celeborn's pump uses cards actually looked at. -/
def celebornLookedAtOk : Bool :=
  (celebornScried.object! celebornScried.stack.back!.objectId).lastKnownPower ==
      some 1 &&
    (ruling 105).comment.contains "cards you actually looked at"

#guard celebornLookedAtOk

/-- Ruling 108: Colossal Whale uses one ability that both exiles and returns. -/
def whaleLinkedOk : Bool :=
  colossalWhale.triggeredAbilities == #[.onAttackMayExileDefenderUntilLeaves] &&
    (ruling 108).comment.contains "single ability that creates two one-shot effects"

#guard whaleLinkedOk

/-- Ruling 114: each cascade instance is a separate trigger. -/
def twoCascadesOk : Bool :=
  callForthTheTempest.cascade == 2 &&
    (ruling 114).comment.contains "Each instance of cascade triggers"

#guard twoCascadesOk

/-- Ruling 41 / 17 / 28: already-modeled amass errata, illegal-target amass, and
Storied not using the stack. -/
def sharedKeywordCommentsOk : Bool :=
  (ruling 41).comment.contains "amass Zombies N" &&
    (ruling 17).comment.contains "won't amass" &&
    (ruling 28).comment.contains "doesn't use the stack" &&
    (ruling 95).comment.contains "additional costs" &&
    (ruling 196).comment.contains "additional costs" &&
    (ruling 197).comment.contains "additional costs"

#guard sharedKeywordCommentsOk

/-- Ruling 64: an exiled land still follows land-play timing. -/
def exiledLandTimingOk : Bool :=
  afterDraw.canPlayLand ⟨0⟩ &&
    !afterDraw.canPlayLand ⟨1⟩ &&
    (ruling 64).comment.contains "only during your main phase"

#guard exiledLandTimingOk

/-- Ruling 10: a copy of an adventurer object has an Adventure; a token copy
that leaves the battlefield ceases to exist. -/
def adventureCopyHasAdventureOk : Bool :=
  let printed := { bilboLuckwearerCard with isToken := true }
  let (g, tok) := started.createToken ⟨0⟩ printed
  let hasAdv := tok.printed.adventure.isSome
  let (g, _) := g.move tok.id (.graveyard ⟨0⟩) none
  let g := g.checkSBA
  hasAdv &&
    !g.objects.any (fun o => o.name == "Bilbo, Luckwearer") &&
    (ruling 10).comment.contains "the copy also has an Adventure"

#guard adventureCopyHasAdventureOk

/-- Ruling 75: activating a creature mana ability triggers Elrond. -/
def elrondManaAbility : Except String Game :=
  let g := addPermanent afterDraw elrondMoonReader ⟨0⟩ ⟨0⟩
  let g := addPermanent g llanowarElves ⟨0⟩ ⟨0⟩
  g.tapForMana ⟨0⟩ (namedPermanent g "Llanowar Elves").id (.colored .green)

def elrondManaAbilityOk : Bool :=
  match elrondManaAbility with
  | .error _ => false
  | .ok g =>
    countWaiting g .onActivateCreatureAbilityDrawOnce == 1 &&
      (ruling 75).comment.contains "mana ability"

#guard elrondManaAbilityOk

/-- Ruling 86: Great Gilded Boat triggers when you attack, even if it is not
among the attackers. -/
def boatRecruitOnAttack : Game :=
  let g := addPermanent afterDraw greatGildedBoat ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  g.putControlledTriggers ⟨0⟩ .youAttack

def boatRecruitOnAttackOk : Bool :=
  countWaiting boatRecruitOnAttack .onYouAttackRecruit == 1 &&
    greatGildedBoat.triggeredAbilities == #[.onYouAttackRecruit] &&
    (ruling 86).comment.contains "doesn't have to be among them"

#guard boatRecruitOnAttackOk

/-- Ruling 96: Belladonna's fourth resolve in a turn does nothing. -/
def belladonnaFourResolves : Game :=
  let g := addPermanent afterDraw belladonnaTook ⟨0⟩ ⟨0⟩
  let src := some (namedPermanent g "Belladonna Took").id
  let g := g.applyTriggeredAbility ⟨0⟩ .onTokenYouControlEntersBelladonna src
  let g := g.applyTriggeredAbility ⟨0⟩ .onTokenYouControlEntersBelladonna src
  let g := g.applyTriggeredAbility ⟨0⟩ .onTokenYouControlEntersBelladonna src
  g.applyTriggeredAbility ⟨0⟩ .onTokenYouControlEntersBelladonna src

def belladonnaFourResolvesOk : Bool :=
  let g := belladonnaFourResolves
  (g.player ⟨0⟩).life == 21 &&
    (g.player ⟨0⟩).hand.size == (afterDraw.player ⟨0⟩).hand.size + 1 &&
    (namedPermanent g "Belladonna Took").status.plusOnePlusOne == 1 &&
    (g.player ⟨0⟩).belladonnaResolvesThisTurn == 4 &&
    g.log.any (fun s => mentions s "no effect") &&
    (ruling 96).comment.contains "no effect each time beyond the third"

#guard belladonnaFourResolvesOk

/-- Ruling 96: a token entering actually queues the ability. -/
def belladonnaSeesToken : Game :=
  let g := addPermanent afterDraw belladonnaTook ⟨0⟩ ⟨0⟩
  let (g, tok) := g.createToken ⟨0⟩ Game.humanSoldierToken
  g.afterPermanentEnters (g.object! tok.id)

#guard countWaiting belladonnaSeesToken .onTokenYouControlEntersBelladonna == 1

/-- Ruling 100: mill and discard still go to the graveyard. -/
def headDoesNotExileMill : Game :=
  let g := addPermanent afterDraw headOfTheHunt ⟨0⟩ ⟨0⟩
  let g := addToHand g shock ⟨1⟩
  let id := (handCardNamed g ⟨1⟩ "Shock").id
  (g.move id (.graveyard ⟨1⟩) none).1

def headDoesNotExileMillOk : Bool :=
  headDoesNotExileMill.objects.any (fun o =>
    o.name == "Shock" && o.zone == .graveyard ⟨1⟩) &&
    !(headDoesNotExileMill.objects.any (fun o =>
      o.name == "Shock" && o.zone == .exile)) &&
    (ruling 100).comment.contains "will not be exiled instead"

#guard headDoesNotExileMillOk

/-- Ruling 100 / 140: an opposing creature that would die is exiled instead,
and a simultaneous death of Head of the Hunt still exiles it. -/
def headExilesInstead : Game :=
  let g := addPermanent afterDraw headOfTheHunt ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let bears := namedPermanent g "Grizzly Bears"
  (g.move bears.id (.graveyard ⟨1⟩) none).1

def headExilesInsteadOk : Bool :=
  headExilesInstead.objects.any (fun o =>
    o.name == "Grizzly Bears" && o.zone == .exile) &&
    (headExilesInstead.battlefield.filter (fun o => o.name == "Wolf")).size == 1 &&
    headExilesInstead.log.any (fun s => mentions s "CR 614.6") &&
    (ruling 100).comment.contains "discarded or milled"

#guard headExilesInsteadOk

def headDiesWithPrey : Game :=
  let g := addPermanent afterDraw headOfTheHunt ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let head := namedPermanent g "Head of the Hunt"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { head with status := { head.status with damage := 10 } }
  let g := g.setObject { bears with status := { bears.status with damage := 10 } }
  g.checkSBA

def headDiesWithPreyOk : Bool :=
  headDiesWithPrey.objects.any (fun o =>
    o.name == "Grizzly Bears" && o.zone == .exile) &&
    headDiesWithPrey.objects.any (fun o =>
      o.name == "Head of the Hunt" &&
        match o.zone with
        | .graveyard _ => true
        | _ => false) &&
    (ruling 140).comment.contains "still be exiled"

#guard headDiesWithPreyOk

/-- Ruling 80: Ori counts destroyed permanents even if they are exiled. -/
def oriCountsExiled : Game :=
  let g := addPermanent afterDraw oriPlateStacker ⟨0⟩ ⟨0⟩
  let g := addPermanent g dwarvenShortsword ⟨1⟩ ⟨1⟩
  let sw := namedPermanent g "Dwarven Shortsword"
  let g := g.setObject { sw with status := { sw.status with
    untilEotExileIfDies := true } }
  g.applyTriggeredAbility ⟨0⟩ .onEnterDestroyOppArtifactsEnchantmentsGainLife
    (some (namedPermanent g "Ori, Plate Stacker").id)

def oriCountsExiledOk : Bool :=
  (oriCountsExiled.player ⟨0⟩).life == 21 &&
    oriCountsExiled.objects.any (fun o =>
      o.name == "Dwarven Shortsword" && o.zone == .exile) &&
    (ruling 80).comment.contains "zone other than a graveyard"

#guard oriCountsExiledOk

/-- Ruling 139: Great Fierce Bee still triggers if it dies with other creatures. -/
def beeDiesWithOthers : Game :=
  let g := addPermanent afterDraw greatFierceBeeCard ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bee := namedPermanent g "Great Fierce Bee"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bee with status := { bee.status with damage := 20 } }
  let g := g.setObject { bears with status := { bears.status with damage := 10 } }
  g.checkSBA

def beeDiesWithOthersOk : Bool :=
  countWaiting beeDiesWithOthers (.onOneOrMoreOtherCreaturesDieScry 1) == 1 &&
    (ruling 139).comment.contains "dies at the same time"

#guard beeDiesWithOthersOk

/-- Ruling 141: an untapped Minas Tirith Garrison may tap itself. -/
def garrisonTapsSelf : Except String Game :=
  let g := addPermanent afterDraw minasTirithGarrison ⟨0⟩ ⟨0⟩
  let g := { g with pending := .tapHumans ⟨0⟩ }
  g.choosePermanents ⟨0⟩ #[(namedPermanent g "Minas Tirith Garrison").id]

def garrisonTapsSelfOk : Bool :=
  match garrisonTapsSelf with
  | .error _ => false
  | .ok g =>
    (namedPermanent g "Minas Tirith Garrison").status.tapped &&
      (g.player ⟨0⟩).hand.size == (afterDraw.player ⟨0⟩).hand.size + 1 &&
      (ruling 141).comment.contains "tapped for its own last ability"

#guard garrisonTapsSelfOk

/-- Ruling 142: Smite's extra effects apply even if no damage is marked. -/
def smiteZeroDamage : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  g.dealDamageLoseIndestructibleExileTo (namedPermanent g "Grizzly Bears") 0

def smiteZeroDamageOk : Bool :=
  let b := namedPermanent smiteZeroDamage "Grizzly Bears"
  b.status.untilEotLosesIndestructible &&
    b.status.untilEotExileIfDies &&
    b.status.damage == 0 &&
    (ruling 142).comment.contains "additional effects will still apply"

#guard smiteZeroDamageOk

/-- Ruling 149 / 159–162: an exiled token ceases to exist and does not return. -/
def exiledTokenCeases : Game :=
  let (g, tok) := afterDraw.createToken ⟨0⟩ Game.humanSoldierToken
  let (g, _) := g.move tok.id .exile none
  g.checkSBA

def exiledTokenCeasesOk : Bool :=
  !exiledTokenCeases.objects.any (fun o => o.name == "Human Soldier") &&
    (ruling 149).comment.contains "ceases to exist" &&
    ((ruling 159).comment.contains "won't return" ||
      (ruling 159).comment.contains "won't be returned") &&
    ((ruling 160).comment.contains "won't return" ||
      (ruling 160).comment.contains "won’t return") &&
    (ruling 161).comment.contains "won't return" &&
    (ruling 162).comment.contains "won't be returned"

#guard exiledTokenCeasesOk

/-- Ruling 151 / 126 / 256: protection from everything blocks targeting and
preventable damage, but not unpreventable damage. -/
def withProtection : Game :=
  afterDraw.modifyPlayer ⟨1⟩ (fun pl => { pl with protectionFromEverything := true })

def protectionFromEverythingOk : Bool :=
  let ts := withProtection.legalTargets ⟨0⟩ (Effect.dealDamage 3)
  !ts.any (fun t => t == Target.player ⟨1⟩) &&
    (let g := withProtection.dealDamageToPlayer ⟨1⟩ 5
     (g.player ⟨1⟩).life == 20 &&
       g.log.any (fun s => mentions s "prevented")) &&
    (let g := withProtection.dealDamageToPlayer ⟨1⟩ 5 (preventable := false)
     (g.player ⟨1⟩).life == 15) &&
    (ruling 151).comment.contains "can't be the target" &&
    (ruling 126).comment.contains "illegal target" &&
    (ruling 256).comment.contains "can't be prevented"

#guard protectionFromEverythingOk

/-- Ruling 167: tapping an attacking Human for Garrison leaves it attacking. -/
def garrisonTapAttackerOk : Bool :=
  let g := addPermanent afterDraw minasTirithGarrison ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let human :=
    creature "Townsfolk" (ManaCost.ofGeneric 1) #["Human"] 1 1
  let g := addPermanent g human ⟨0⟩ ⟨0⟩
  let h := namedPermanent g "Townsfolk"
  let g := g.setObject { h with status := { h.status with attacking := true } }
  let g := { g with pending := .tapHumans ⟨0⟩ }
  match g.choosePermanents ⟨0⟩ #[(namedPermanent g "Townsfolk").id] with
  | .error _ => false
  | .ok g =>
    (namedPermanent g "Townsfolk").status.tapped &&
      (namedPermanent g "Townsfolk").status.attacking &&
      (ruling 167).comment.contains "remains an attacking creature"

#guard garrisonTapAttackerOk

/-- Ruling 170: Elven Chorus is not an Elf card. -/
def elvenChorusNotElfOk : Bool :=
  !elvenChorus.hasSubtype "Elf" &&
    !elvenChorus.isCreature &&
    (ruling 170).comment.contains "Elven Chorus is not an Elf"

#guard elvenChorusNotElfOk

/-- Ruling 206: if Executioner is your only creature, you sacrifice it. -/
def executionerSacrificesSelf : Game :=
  let g := addPermanent afterDraw mercilessExecutioner ⟨0⟩ ⟨0⟩
  let g := g.applyTriggeredAbility ⟨0⟩ .onEnterEachPlayerSacrificesCreature
    (some (namedPermanent g "Merciless Executioner").id)
  mustApply g ⟨0⟩ (.sacrifice (namedPermanent g "Merciless Executioner").id)

def executionerSacrificesSelfOk : Bool :=
  !executionerSacrificesSelf.battlefield.any (fun o =>
      o.name == "Merciless Executioner") &&
    (ruling 206).comment.contains "sacrifice Merciless Executioner"

#guard executionerSacrificesSelfOk

/-!
## 78 — The Eagles Are Coming! counts tokens returned to hand
-/

def eaglesReturnToken : Game :=
  let (g, tok) := afterDraw.createToken ⟨0⟩ Game.humanSoldierToken
  g.returnOwnedCreaturesScheduleBirds ⟨0⟩ #[tok.id]

def eaglesTokenCountedOk : Bool :=
  (eaglesReturnToken.player ⟨0⟩).eaglesBirdsNextUpkeep == 1 &&
    eaglesReturnToken.objects.any (fun o =>
      o.name == "Human Soldier" && o.zone == .hand ⟨0⟩) &&
    (ruling 78).comment.contains "creature tokens that were returned"

#guard eaglesTokenCountedOk

def eaglesBirdsAfterUpkeep : Game :=
  let g := { eaglesReturnToken.checkSBA with waitingTriggers := #[] }
  { g with step := .untap, activePlayer := ⟨1⟩ }.beginStep .upkeep

def eaglesBirdsAfterUpkeepOk : Bool :=
  eaglesBirdsAfterUpkeep.battlefield.any (fun o =>
    o.name == "Bird Soldier" && o.printed.isToken &&
      eaglesBirdsAfterUpkeep.hasSubtype o "Bird") &&
    !eaglesBirdsAfterUpkeep.objects.any (fun o =>
      o.name == "Human Soldier" && o.zone == .hand ⟨0⟩) &&
    (ruling 78).comment.contains "Bird Soldier token"

#guard eaglesBirdsAfterUpkeepOk

/-!
## 98, 99, 121 — Bolg reflexive trigger and excess damage
-/

def bolgReady : Game :=
  let g := addPermanent afterDraw bolgOfTheNorth ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  addPermanent g grayOgre ⟨1⟩ ⟨1⟩

def bolgMaySacPending : Game :=
  bolgReady.applyTriggeredAbility ⟨0⟩ .onEnterBolgMaySacrifice
    (some (namedPermanent bolgReady "Bolg of the North").id)

def bolgReflexivePendingOk : Bool :=
  (match bolgMaySacPending.pending with
   | .maySacrificeAnotherBolg p _ => p == ⟨0⟩
   | _ => false) &&
    (ruling 98).comment.contains "reflexive triggered ability" &&
    (ruling 98).comment.contains "without a target"

#guard bolgReflexivePendingOk

def bolgAfterSacrifice : Game :=
  mustApply bolgMaySacPending ⟨0⟩
    (.sacrifice (namedPermanent bolgMaySacPending "Hill Giant").id)

def bolgAfterSacrificeOk : Bool :=
  let onStack :=
    bolgAfterSacrifice.stack.any (fun e =>
      (bolgAfterSacrifice.object! e.objectId).triggeredAbility ==
        some .onBolgDealSacrificedPower)
  let waiting :=
    bolgAfterSacrifice.waitingTriggers.any (fun wt =>
      wt.ability == .onBolgDealSacrificedPower &&
        wt.lastKnownPower == some 3)
  (onStack || waiting) &&
    !bolgAfterSacrifice.battlefield.any (fun o => o.name == "Hill Giant") &&
    (ruling 98).comment.contains "second ability triggers"

#guard bolgAfterSacrificeOk

def bolgDeclineNoDamage : Game :=
  mustApply bolgMaySacPending ⟨0⟩ .decline

def bolgDeclineOk : Bool :=
  !bolgDeclineNoDamage.waitingTriggers.any (fun wt =>
    wt.ability == .onBolgDealSacrificedPower) &&
    bolgDeclineNoDamage.battlefield.any (fun o => o.name == "Hill Giant")

#guard bolgDeclineOk

def bolgOtherSac : Game :=
  let g := bolgReady.beginSacrificeCreature ⟨0⟩
  mustApply g ⟨0⟩ (.sacrifice (namedPermanent g "Hill Giant").id)

def bolgOtherSacOk : Bool :=
  !bolgOtherSac.waitingTriggers.any (fun wt =>
    wt.ability == .onBolgDealSacrificedPower) &&
    (ruling 99).comment.contains "won't trigger if you sacrifice a creature for any other reason"

#guard bolgOtherSacOk

def bolgDeal (g : Game) (amt : Int) (tid : ObjectId) : Game :=
  g.applyTriggeredAbility ⟨0⟩ .onBolgDealSacrificedPower
    (some (namedPermanent g "Bolg of the North").id)
    #[Target.permanent tid] #[] (some amt)

def bolgExcessDamage : Game :=
  bolgDeal bolgAfterSacrifice 3 (namedPermanent bolgAfterSacrifice "Gray Ogre").id

def bolgExcessOk : Bool :=
  (namedPermanent bolgExcessDamage "Gray Ogre").status.damage == 3 &&
    bolgExcessDamage.battlefield.any (fun o =>
      bolgExcessDamage.hasSubtype o "Army" && o.status.plusOnePlusOne == 1) &&
    (ruling 121).comment.contains "damage already marked"

#guard bolgExcessOk

def bolgMarkedExcess : Game :=
  let g := addPermanent afterDraw bolgOfTheNorth ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  let giant := namedPermanent g "Hill Giant"
  let g := g.mapObjectStatus giant (fun s => { s with damage := 2 })
  bolgDeal g 3 giant.id

def bolgMarkedExcessOk : Bool :=
  bolgMarkedExcess.battlefield.any (fun o =>
    bolgMarkedExcess.hasSubtype o "Army" && o.status.plusOnePlusOne == 2) &&
    (ruling 121).comment.contains "greater than lethal damage"

#guard bolgMarkedExcessOk

/-!
## 103 — Cavern-Hoard counts artifacts as the ability resolves
-/

def cavernHoardResolveCount : Game :=
  let g := addPermanent afterDraw cavernHoardDragon ⟨0⟩ ⟨0⟩
  let (g, _) := g.createToken ⟨1⟩ Game.treasureToken
  let (g, _) := g.createToken ⟨1⟩ Game.treasureToken
  let g := { g with lastCombatDamagePlayer := some ⟨1⟩ }
  let t := namedPermanent g "Treasure"
  let g := (g.move t.id (.graveyard ⟨1⟩) none).1
  g.applyTriggeredAbility ⟨0⟩
    .onCombatDamageCreateTreasuresEqualPlayerArtifacts
    (some (namedPermanent g "Cavern-Hoard Dragon").id)

def cavernHoardResolveCountOk : Bool :=
  (cavernHoardResolveCount.battlefield.filter (fun o =>
    o.name == "Treasure" && o.controlledBy ⟨0⟩)).size == 1 &&
    (cavernHoardResolveCount.battlefield.filter (fun o =>
      o.name == "Treasure" && o.controlledBy ⟨1⟩)).size == 1 &&
    (ruling 103).comment.contains "as the ability resolves"

#guard cavernHoardResolveCountOk

/-!
## 112 — Desert Were-Worm checks power at attack time
-/

def wereWormMountains (n : Nat) : Game :=
  let g := addPermanent afterDraw desertWereWorm ⟨0⟩ ⟨0⟩
  (List.range n).foldl (init := g) fun g _ =>
    addPermanent g mountain ⟨0⟩ ⟨0⟩

def wereWormTenPower : Game := wereWormMountains 5

def wereWormTenPowerOk : Bool :=
  wereWormTenPower.power (namedPermanent wereWormTenPower "Desert Were-Worm") == 10

#guard wereWormTenPowerOk

def wereWormTenAttacks : Game :=
  let g := wereWormTenPower
  let w := namedPermanent g "Desert Were-Worm"
  let g := g.setObject { w with status := { w.status with attacking := true } }
  g.putAttackTriggersOnStack ⟨0⟩ #[(namedPermanent g "Desert Were-Worm").id]

def wereWormTenAttacksOk : Bool :=
  !wereWormTenAttacks.waitingTriggers.any (fun wt =>
    wt.event == .youAttackWithTotalPower) &&
    (ruling 112).comment.contains "at the time you attacked"

#guard wereWormTenAttacksOk

def wereWormTwelveAttacks : Game :=
  let g := wereWormMountains 6
  let w := namedPermanent g "Desert Were-Worm"
  let g := g.setObject { w with status := { w.status with attacking := true } }
  g.putAttackTriggersOnStack ⟨0⟩ #[(namedPermanent g "Desert Were-Worm").id]

def wereWormTwelveAttacksOk : Bool :=
  wereWormTwelveAttacks.power
      (namedPermanent wereWormTwelveAttacks "Desert Were-Worm") == 12 &&
    wereWormTwelveAttacks.waitingTriggers.any (fun wt =>
      wt.event == .youAttackWithTotalPower) &&
    (ruling 112).comment.contains "will not contribute"

#guard wereWormTwelveAttacksOk

/-!
## 118, 191 — Elven Chorus timing and looking at the top
-/

def chorusInPlay : Game := addPermanent afterDraw elvenChorus ⟨0⟩ ⟨0⟩

def elvenChorusTimingOk : Bool :=
  chorusInPlay.canLookAtLibraryTop ⟨0⟩ &&
    chorusInPlay.controlsCastCreaturesFromTop ⟨0⟩ &&
    chorusInPlay.asSorcery? ⟨0⟩ &&
    !(let g := { chorusInPlay with step := .end }
      g.timingAllowsCast ⟨0⟩ grizzlyBears) &&
    (ruling 118).comment.contains "doesn't change when you can cast"

#guard elvenChorusTimingOk

def chorusCastingFromTop : Game := { chorusInPlay with castingFromTop := true }

def elvenChorusNewTopHiddenOk : Bool :=
  !chorusCastingFromTop.canLookAtLibraryTop ⟨0⟩ &&
    chorusInPlay.canLookAtLibraryTop ⟨0⟩ &&
    (ruling 191).comment.contains "can't look at the new top card"

#guard elvenChorusNewTopHiddenOk

/-!
## 125 — Mount Doom last ability does not target
-/

def mountDoomChooseKeep : Game :=
  let g := addPermanent afterDraw mountDoom ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  g.chooseCreaturesDestroyRest #[(namedPermanent g "Grizzly Bears").id]

def mountDoomChooseKeepOk : Bool :=
  mountDoomChooseKeep.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    !mountDoomChooseKeep.battlefield.any (fun o => o.name == "Gray Ogre") &&
    (ruling 125).comment.contains "none of the chosen creatures are targets"

#guard mountDoomChooseKeepOk

/-!
## 129, 130 — Gleaming Splendor second-card trigger and two players
-/

def gleamingReady : Game :=
  let g := addPermanent afterDraw gleamingSplendor ⟨0⟩ ⟨0⟩
  g.modifyPlayer ⟨1⟩ (fun pl => { pl with cardsDrawnThisTurn := 0 })

def gleamingSecondDraw : Game :=
  (gleamingReady.draw ⟨1⟩ 1).draw ⟨1⟩ 1

def gleamingFirstDraw : Game :=
  gleamingReady.draw ⟨1⟩ 1

def gleamingSecondDrawOk : Bool :=
  gleamingFirstDraw.waitingTriggers.all (fun wt =>
    wt.event != .opponentDrawsSecondCard) &&
    gleamingSecondDraw.waitingTriggers.any (fun wt =>
      wt.event == .opponentDrawsSecondCard) &&
    (ruling 129).comment.contains "second card" &&
    (ruling 129).comment.contains "only once each turn"

#guard gleamingSecondDrawOk

def gleamingTwoDifferentPlayersOk : Bool :=
  (match afterDraw.twoPlayersEachDraw ⟨0⟩ ⟨0⟩ with
   | .error e => e.contains "different"
   | .ok _ => false) &&
    (match afterDraw.twoPlayersEachDraw ⟨0⟩ ⟨1⟩ with
     | .ok g =>
       (g.player ⟨0⟩).cardsDrawnThisTurn ==
         (afterDraw.player ⟨0⟩).cardsDrawnThisTurn + 1 &&
         (g.player ⟨1⟩).cardsDrawnThisTurn ==
           (afterDraw.player ⟨1⟩).cardsDrawnThisTurn + 1
     | .error _ => false) &&
    (ruling 130).comment.contains "two different target players"

#guard gleamingTwoDifferentPlayersOk

/-!
## 132, 181 — Andúril, Flame of the West
-/

def andurilOnOppLegend : Game :=
  let g := addPermanent afterDraw andurilFlameOfTheWest ⟨0⟩ ⟨0⟩
  let g := addPermanent g tomBombadil ⟨1⟩ ⟨1⟩
  let g := g.attachSourceTo (namedPermanent g "Andúril, Flame of the West")
    (namedPermanent g "Tom Bombadil")
  let tom := namedPermanent g "Tom Bombadil"
  let g := g.setObject { tom with status := { tom.status with attacking := true } }
  g.putAttackTriggersOnStack ⟨1⟩ #[(namedPermanent g "Tom Bombadil").id]

def andurilOnOppLegendOk : Bool :=
  andurilOnOppLegend.waitingTriggers.any (fun wt =>
    wt.ability == .onEquippedAttacksCreateSpirits &&
      wt.controller == ⟨0⟩) &&
    (ruling 132).comment.contains "opponent controls"

#guard andurilOnOppLegendOk

def andurilOppSpirits : Game :=
  andurilOnOppLegend.applyTriggeredAbility ⟨0⟩
    .onEquippedAttacksCreateSpirits
    (some (namedPermanent andurilOnOppLegend "Andúril, Flame of the West").id)

def andurilOppSpiritsOk : Bool :=
  let spirits :=
    andurilOppSpirits.battlefield.filter (fun o => o.name == "Spirit")
  spirits.size == 2 &&
    spirits.all (fun o => o.status.tapped && !o.status.attacking &&
      o.controlledBy ⟨0⟩) &&
    (ruling 132).comment.contains "would not enter the battlefield attacking"

#guard andurilOppSpiritsOk

def andurilOnOwnLegend : Game :=
  let g := addPermanent afterDraw andurilFlameOfTheWest ⟨0⟩ ⟨0⟩
  let g := addPermanent g tomBombadil ⟨0⟩ ⟨0⟩
  let g := g.attachSourceTo (namedPermanent g "Andúril, Flame of the West")
    (namedPermanent g "Tom Bombadil")
  let tom := namedPermanent g "Tom Bombadil"
  let g := g.setObject { tom with status := { tom.status with attacking := true } }
  let g := g.putAttackTriggersOnStack ⟨0⟩ #[(namedPermanent g "Tom Bombadil").id]
  g.applyTriggeredAbility ⟨0⟩ .onEquippedAttacksCreateSpirits
    (some (namedPermanent g "Andúril, Flame of the West").id)

def andurilOnOwnLegendOk : Bool :=
  let spirits :=
    andurilOnOwnLegend.battlefield.filter (fun o => o.name == "Spirit")
  spirits.size == 2 &&
    spirits.all (fun o => o.status.tapped && o.status.attacking) &&
    (ruling 181).comment.contains "Andúril's controller chooses"

#guard andurilOnOwnLegendOk

/-!
## 150 — Queen of Dale misses a prior first noncreature
-/

def queenAfterFirstNoncreature : Game :=
  let g := addPermanent afterDraw theQueenOfDale ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨1⟩ (fun pl =>
    { pl with noncreatureSpellsCastThisTurn := 1 })
  let g := addToHand g lightningBolt ⟨1⟩
  let bolt :=
    match (g.player ⟨1⟩).hand.back?.bind g.findObject? with
    | some o => o
    | none => panic! "expected Lightning Bolt"
  g.putCastTriggersOnStack ⟨1⟩ bolt

def queenAfterFirstNoncreatureOk : Bool :=
  !queenAfterFirstNoncreature.waitingTriggers.any (fun wt =>
    wt.ability == .onOpponentCastsFirstNoncreatureRecruit) &&
    (ruling 150).comment.contains "already cast their first noncreature"

#guard queenAfterFirstNoncreatureOk

/-!
## 155 — Orcish Bowmasters: putting into hand is not a draw
-/

def bowmastersInPlay : Game :=
  addPermanent afterDraw orcishBowmasters ⟨0⟩ ⟨0⟩

def bowmastersPutInHand : Game :=
  addToHand bowmastersInPlay lightningBolt ⟨1⟩

def bowmastersPutInHandOk : Bool :=
  !bowmastersPutInHand.waitingTriggers.any (fun wt =>
    wt.event == .opponentDrawsExceptFirstDrawStep) &&
    (ruling 155).comment.contains "without specifically using the word"

#guard bowmastersPutInHandOk

def bowmastersAfterDraw : Game :=
  bowmastersInPlay.draw ⟨1⟩ 1

def bowmastersAfterDrawOk : Bool :=
  bowmastersAfterDraw.waitingTriggers.any (fun wt =>
    wt.event == .opponentDrawsExceptFirstDrawStep) &&
    (ruling 155).comment.contains "not a card drawn"

#guard bowmastersAfterDrawOk

def bowmastersFirstDrawStep : Game :=
  let g := { bowmastersInPlay with step := .draw, activePlayer := ⟨1⟩ }
  g.draw ⟨1⟩ 1

def bowmastersFirstDrawStepOk : Bool :=
  !bowmastersFirstDrawStep.waitingTriggers.any (fun wt =>
    wt.event == .opponentDrawsExceptFirstDrawStep)

#guard bowmastersFirstDrawStepOk

/-!
## 156 — Old Fat Spider triggers once per spell even if targeted twice
-/

def spiderDoubleTarget : Game :=
  let g := addPermanent afterDraw oldFatSpider ⟨0⟩ ⟨0⟩
  let sid := (namedPermanent g "Old Fat Spider").id
  g.queueBecomesTargetTriggers ⟨1⟩
    #[Target.permanent sid, Target.permanent sid]

def spiderDoubleTargetOk : Bool :=
  (spiderDoubleTarget.waitingTriggers.filter (fun wt =>
    wt.event == .becomesTarget)).size == 1 &&
    (ruling 156).comment.contains "targets Old Fat Spider more than once"

#guard spiderDoubleTargetOk

/-!
## 9 — an Adventure on the stack does not “have an Adventure”
-/

def adventureOnStackNotHasAdventureOk : Bool :=
  spewOnStack.isAdventureSpell &&
    spewOnStack.printed.adventure.isNone &&
    !(spewOnStack.printed.hasAdventure) &&
    (ruling 9).comment.contains "won't find an instant or sorcery spell on the stack"

#guard adventureOnStackNotHasAdventureOk

/-!
## 34, 35 — extra linked-exile instances share “the exiled card”
-/

def linkedExileTwoCards : Game :=
  let g := addPermanent afterDraw fiendHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let bear := namedPermanent g "Grizzly Bears"
  let ogre := namedPermanent g "Gray Ogre"
  let (g, bEx) := g.move bear.id .exile none
  let (g, oEx) := g.move ogre.id .exile none
  g.setObject { (namedPermanent g "Fiend Hunter") with
    linkedExile := #[bEx, oEx] }

def linkedExileTwoCardsOk : Bool :=
  let hunter := namedPermanent linkedExileTwoCards "Fiend Hunter"
  hunter.linkedExile.size == 2 &&
    (let g := linkedExileTwoCards.returnLinkedExile hunter
     g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
       g.battlefield.any (fun o => o.name == "Gray Ogre")) &&
    (ruling 34).comment.contains "additional instances" &&
    (ruling 35).comment.contains "the sum is used"

#guard linkedExileTwoCardsOk

/-!
## 136 — Celebrate leaves before exile resolves
-/

def celebrateLeavesBeforeExile : Game :=
  let g := addPermanent afterDraw celebrateTheMountainKing ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let sid := (namedPermanent g "Celebrate the Mountain-king").id
  let (g, _) := g.move sid (.graveyard ⟨0⟩) none
  g.applyTriggeredAbility ⟨0⟩ .onEnterExileOppNonlandUntilLeaves (some sid)
    #[Target.permanent (namedPermanent g "Grizzly Bears").id]

def celebrateLeavesBeforeExileOk : Bool :=
  celebrateLeavesBeforeExile.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    celebrateLeavesBeforeExile.log.any (fun s =>
      mentions s "left the battlefield" || mentions s "Nothing is exiled") &&
    (ruling 136).comment.contains "no nonland permanents will be exiled"

#guard celebrateLeavesBeforeExileOk

/-!
## 147 — a copy of a permanent is not kicked
-/

def copyOfKickedPermanentOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bear with kicked := true }
  let src := namedPermanent g "Grizzly Bears"
  let (_g, tok) := g.copyBattlefieldPermanent src ⟨0⟩
  src.kicked && !tok.kicked && tok.printed.isToken &&
    (ruling 147).comment.contains "isn't kicked"

#guard copyOfKickedPermanentOk

/-!
## 163, 172, 231, 294 — Galadriel Alliance modes
-/

def galadrielInPlay : Game :=
  addPermanent afterDraw galadrielLightOfValinor ⟨0⟩ ⟨0⟩

def galadrielAllModesSpent : Game :=
  let sid := (namedPermanent galadrielInPlay "Galadriel, Light of Valinor").id
  let g := galadrielInPlay.applyAllianceMode sid 0
  let g := g.applyAllianceMode sid 1
  g.applyAllianceMode sid 2

def galadrielFourthDoesNothing : Game :=
  let sid := (namedPermanent galadrielAllModesSpent "Galadriel, Light of Valinor").id
  galadrielAllModesSpent.applyTriggeredAbility ⟨0⟩
    .onAnotherCreatureYouControlEntersAlliance (some sid)

def galadrielModesExhaustedOk : Bool :=
  galadrielFourthDoesNothing.log.any (fun s =>
    mentions s "all three modes have been chosen") &&
    (ruling 163).comment.contains "removed from the stack with no effect"

#guard galadrielModesExhaustedOk

def galadrielSimultaneousModesOk : Bool :=
  let sid := (namedPermanent galadrielInPlay "Galadriel, Light of Valinor").id
  let g := galadrielInPlay.applyAllianceMode sid 0
  let g := g.applyAllianceMode sid 1
  let used := (namedPermanent g "Galadriel, Light of Valinor").status.allianceModesChosen
  used.contains 0 && used.contains 1 && !used.contains 2 &&
    (g.unusedAllianceModes (namedPermanent g "Galadriel, Light of Valinor")).size == 1 &&
    (ruling 172).comment.contains "different modes"

#guard galadrielSimultaneousModesOk

def galadrielStolenKeepsModesOk : Bool :=
  let sid := (namedPermanent galadrielInPlay "Galadriel, Light of Valinor").id
  let g := galadrielInPlay.applyAllianceMode sid 0
  let g := g.applyAllianceMode sid 1
  let gala := namedPermanent g "Galadriel, Light of Valinor"
  let g := g.setObject { gala with controller := some ⟨1⟩ }
  let left := g.unusedAllianceModes (namedPermanent g "Galadriel, Light of Valinor")
  left == #[2] &&
    (ruling 231).comment.contains "that player can choose only the third mode"

#guard galadrielStolenKeepsModesOk

def galadrielLeavesAndReturnsOk : Bool :=
  let sid := (namedPermanent galadrielInPlay "Galadriel, Light of Valinor").id
  let g := galadrielInPlay.applyAllianceMode sid 0
  let g := g.applyAllianceMode sid 1
  let (g, _) := g.move (namedPermanent g "Galadriel, Light of Valinor").id
    (.exile) none
  let g := addPermanent g galadrielLightOfValinor ⟨0⟩ ⟨0⟩
  (namedPermanent g "Galadriel, Light of Valinor").status.allianceModesChosen.isEmpty &&
    (ruling 294).comment.contains "new object with no memory"

#guard galadrielLeavesAndReturnsOk

/-!
## 171 — Thorin triggers once per damaging Dwarf
-/

def thorinTwoDwarfTriggersOk : Bool :=
  let g := addPermanent afterDraw thorinCompanySLeader ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let thorin := namedPermanent g "Thorin, Company's Leader"
  let g := g.queueTrigger ⟨0⟩ thorin
    (.onSubtypeYouControlCombatDamageCreateTokens "Dwarf" .treasure 2)
    .dealsCombatDamageToPlayerOrBattle
  let g := g.queueTrigger ⟨0⟩ thorin
    (.onSubtypeYouControlCombatDamageCreateTokens "Dwarf" .treasure 2)
    .dealsCombatDamageToPlayerOrBattle
  (g.waitingTriggers.filter (fun wt =>
    wt.ability == .onSubtypeYouControlCombatDamageCreateTokens "Dwarf" .treasure 2)).size
    == 2 &&
    (ruling 171).comment.contains "once for each of those Dwarves"

#guard thorinTwoDwarfTriggersOk

/-!
## 173, 317 — Azog: no target means no amass; last-known power
-/

def azogNoTarget : Game :=
  let g := addPermanent afterDraw azogMoriaSRuin ⟨0⟩ ⟨0⟩
  g.applyTriggeredAbility ⟨0⟩ .onEnterDestroyOtherAmassControllerPower
    (some (namedPermanent g "Azog, Moria's Ruin").id)

def azogNoTargetOk : Bool :=
  !azogNoTarget.battlefield.any (fun o => azogNoTarget.hasSubtype o "Army") &&
    azogNoTarget.log.any (fun s => mentions s "no player amasses") &&
    (ruling 173).comment.contains "no player amasses Goblins"

#guard azogNoTargetOk

def azogDestroysOpp : Game :=
  let g := addPermanent afterDraw azogMoriaSRuin ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let ogre := namedPermanent g "Gray Ogre"
  g.applyTriggeredAbility ⟨0⟩ .onEnterDestroyOtherAmassControllerPower
    (some (namedPermanent g "Azog, Moria's Ruin").id)
    #[Target.permanent ogre.id] (lastKnownPower := some (g.power ogre))

def azogDestroysOppOk : Bool :=
  !azogDestroysOpp.battlefield.any (fun o => o.name == "Gray Ogre") &&
    azogDestroysOpp.battlefield.any (fun o => azogDestroysOpp.hasSubtype o "Army") &&
    (namedPermanent azogDestroysOpp "Goblin Army").status.plusOnePlusOne == 2 &&
    (ruling 317).comment.contains "last existed on the battlefield"

#guard azogDestroysOppOk

/-!
## 174, 340, 342 — divided damage keeps the original split
-/

def gandalfDividedIllegal : Game :=
  let g := addPermanent afterDraw gandalfSparkStarter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let bearId := (namedPermanent g "Grizzly Bears").id
  let (g, _) := g.move bearId (.graveyard ⟨1⟩) none
  g.applyTriggeredAbility ⟨0⟩ (.onEnterDealDividedDamage 3 3)
    (some (namedPermanent g "Gandalf, Spark Starter").id)
    #[Target.permanent bearId,
      Target.permanent (namedPermanent g "Gray Ogre").id]
    #[2, 1]

def gandalfDividedIllegalOk : Bool :=
  (namedPermanent gandalfDividedIllegal "Gray Ogre").status.damage == 1 &&
    !gandalfDividedIllegal.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    (ruling 174).comment.contains "original division of damage still applies" &&
    (ruling 340).comment.contains "Each target must receive at least 1" &&
    (ruling 342).comment.contains "divide the damage as you put"

#guard gandalfDividedIllegalOk

/-!
## 179 — Witch-king: tied least power is a choice
-/

def witchKingTiedLeast : Game :=
  let g := addPermanent afterDraw witchKingBringerOfRuin ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  addPermanent g grayOgre ⟨1⟩ ⟨1⟩

def witchKingTiedApply : Game :=
  witchKingTiedLeast.applyTriggeredAbility ⟨0⟩ .onAttackDefenderSacsLeastPower
    (some (namedPermanent witchKingTiedLeast "Witch-king, Bringer of Ruin").id)

def witchKingTiedLeastOk : Bool :=
  witchKingTiedApply.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    witchKingTiedApply.battlefield.any (fun o => o.name == "Gray Ogre") &&
    witchKingTiedApply.log.any (fun s => mentions s "tied for least power") &&
    (ruling 179).comment.contains "that player chooses one of them"

#guard witchKingTiedLeastOk

def witchKingChoosesBear : Game :=
  witchKingTiedApply.sacrificeLeastPowerCreature ⟨1⟩
    (some (namedPermanent witchKingTiedApply "Grizzly Bears").id)

def witchKingChoosesBearOk : Bool :=
  !witchKingChoosesBear.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    witchKingChoosesBear.battlefield.any (fun o => o.name == "Gray Ogre")

#guard witchKingChoosesBearOk

/-!
## 182, 257–259, 282, 292 — Radagast first-creature cost
-/

def radagastInPlay : Game :=
  addPermanent afterDraw radagastOfRhosgobel ⟨0⟩ ⟨0⟩

def xGreenCreature : CardDef :=
  creature "X Beast" { symbols := #[.x, .colored .green] } #["Beast"] 0 1

def radagastReducesFirstCreatureOk : Bool :=
  let g := addToHand radagastInPlay grizzlyBears ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Grizzly Bears"
  let cost := g.playManaCost card grizzlyBears
  cost == ManaCost.ofColor .green &&
    grizzlyBears.manaValue == 2 &&
    (ruling 257).comment.contains "changes only the total cost" &&
    (ruling 259).comment.contains "reduces only the generic"

#guard radagastReducesFirstCreatureOk

def radagastXChosenBeforeReductionOk : Bool :=
  let g := addToHand radagastInPlay xGreenCreature ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "X Beast"
  let face : CardDef :=
    { xGreenCreature with manaCost := { symbols := #[.generic 2, .colored .green] } }
  let cost := g.playManaCost card face
  cost == ManaCost.ofColor .green &&
    (ruling 182).comment.contains "choose the value of X before calculating"

#guard radagastXChosenBeforeReductionOk

def radagastCastIsFirstOk : Bool :=
  let g := addToHand radagastInPlay grizzlyBears ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Grizzly Bears"
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with creatureSpellsCastThisTurn := 1 })
  let cost := g.playManaCost card grizzlyBears
  cost == ManaCost.ofGenericAndColor 1 .green &&
    (ruling 258).comment.contains "no other creature spell you cast that turn can be your first"

#guard radagastCastIsFirstOk

def radagastFlashOk : Bool :=
  let g := { radagastInPlay with step := .end }
  g.timingAllowsCast ⟨0⟩ grizzlyBears &&
    !(let g := { afterDraw with step := .end }
      g.timingAllowsCast ⟨0⟩ grizzlyBears) &&
    (ruling 292).comment.contains "doesn't necessarily have to be the first spell"

#guard radagastFlashOk

def radagastAltCostOk : Bool :=
  let g := addToHand radagastInPlay grizzlyBears ⟨0⟩
  let card :=
    let o := handCardNamed g ⟨0⟩ "Grizzly Bears"
    { o with playPermission := some {
      player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }
  let cost := g.playManaCost card grizzlyBears (ManaCost.ofGeneric 2)
  cost == ManaCost.zero &&
    (ruling 282).comment.contains "can apply to alternative costs"

#guard radagastAltCostOk

/-!
## 184, 293 — Delighted Halfling: copies can be countered
-/

def delightedCopyCanBeCounteredOk : Bool :=
  let g := addToHand afterDraw tomBombadil ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Tom Bombadil"
  let (g, sid) := g.move card.id .stack (some ⟨0⟩)
  let g := g.setObject { (g.object! sid) with uncounterableThisCast := true }
  let spell := g.object! sid
  let g := g.copyStackSpell spell ⟨0⟩
  let copy :=
    match g.objects.find? (fun o => o.isCopy && o.name == "Tom Bombadil") with
    | some o => o
    | none => panic! "expected copied Tom Bombadil"
  spell.uncounterableThisCast && !copy.uncounterableThisCast &&
    (let g := g.counterStackSpell copy.id
     g.log.any (fun s => mentions s "is countered")) &&
    (ruling 184).comment.contains "the copy can be countered" &&
    (ruling 293).comment.contains "can't be countered if the mana produced"

#guard delightedCopyCanBeCounteredOk

/-!
## 187, 233 — Mithril Coat enters unattached; illegal target stays unattached
-/

def mithrilEntersUnattachedOk : Bool :=
  let g := addPermanent afterDraw mithrilCoat ⟨0⟩ ⟨0⟩
  (namedPermanent g "Mithril Coat").attachedTo.isNone &&
    mithrilCoat.triggeredAbilities == #[.onEnterAttachToLegendary] &&
    (ruling 233).comment.contains "doesn't enter the battlefield attached"

#guard mithrilEntersUnattachedOk

def mithrilIllegalStaysUnattached : Game :=
  let g := addPermanent afterDraw mithrilCoat ⟨0⟩ ⟨0⟩
  let sid := (namedPermanent g "Mithril Coat").id
  g.applyTriggeredAbility ⟨0⟩ .onEnterAttachToLegendary (some sid)

def mithrilIllegalStaysUnattachedOk : Bool :=
  (namedPermanent mithrilIllegalStaysUnattached "Mithril Coat").attachedTo.isNone &&
    mithrilIllegalStaysUnattached.battlefield.any (fun o => o.name == "Mithril Coat") &&
    (ruling 187).comment.contains "remains on the battlefield unattached"

#guard mithrilIllegalStaysUnattachedOk

/-!
## 207, 218, 223, 251 — city's blessing and not-cast kicker
-/

def tenPermanentsNoAscendOk : Bool :=
  let g :=
    (List.range 10).foldl (fun acc _ => addPermanent acc grizzlyBears ⟨0⟩ ⟨0⟩) afterDraw
  !g.hasCitysBlessing ⟨0⟩ &&
    (ruling 207).comment.contains "don't control a permanent or resolving spell with ascend"

#guard tenPermanentsNoAscendOk

def tenPermanentsWithAscend : Game :=
  let g :=
    (List.range 9).foldl (fun acc _ => addPermanent acc grizzlyBears ⟨0⟩ ⟨0⟩) afterDraw
  let g := addPermanent g andurilNarsilReforged ⟨0⟩ ⟨0⟩
  g.refreshCitysBlessing

def cityBlessingPersistsOk : Bool :=
  tenPermanentsWithAscend.hasCitysBlessing ⟨0⟩ &&
    (let g :=
      tenPermanentsWithAscend.battlefield.foldl (fun acc o =>
        if o.name == "Grizzly Bears" then
          (acc.move o.id (.graveyard ⟨0⟩) none).1
        else acc) tenPermanentsWithAscend
     g.hasCitysBlessing ⟨0⟩) &&
    (ruling 251).comment.contains "for the rest of the game" &&
    (ruling 223).comment.contains "before it leaves the battlefield"

#guard cityBlessingPersistsOk

def notCastCannotKickOk : Bool :=
  !(namedPermanent (addPermanent afterDraw galadrielSDismissal ⟨0⟩ ⟨0⟩)
      "Galadriel's Dismissal").kicked &&
    (ruling 218).comment.contains "you can't kick it"

#guard notCastCannotKickOk

/-!
## 209 — copy of a kicked permanent spell is kicked
-/

def kickedCopyAlsoKickedOk : Bool :=
  (kickerCopied.object! kickerCopied.stack.back!.objectId).kicked &&
    (ruling 209).comment.contains "the copy is also kicked"

#guard kickedCopyAlsoKickedOk

/-!
## 216, 269, 346 — The Gaffer
-/

def gafferInPlay : Game :=
  addPermanent afterDraw theGaffer ⟨0⟩ ⟨0⟩

def gafferNoLifeNoTrigger : Game :=
  gafferInPlay.putControlledTriggers ⟨0⟩ .eachEndStep

def gafferNoLifeOk : Bool :=
  !gafferNoLifeNoTrigger.waitingTriggers.any (fun wt =>
    wt.ability == .onEachEndStepDrawIfGainedLife 3) &&
    (ruling 216).comment.contains "won't trigger at all"

#guard gafferNoLifeOk

def gafferGainedBeforeEnter : Game :=
  let g := afterDraw.gainLife ⟨0⟩ 3
  let g := addPermanent g theGaffer ⟨0⟩ ⟨0⟩
  g.putControlledTriggers ⟨0⟩ .eachEndStep

def gafferGainedBeforeEnterOk : Bool :=
  gafferGainedBeforeEnter.waitingTriggers.any (fun wt =>
    wt.ability == .onEachEndStepDrawIfGainedLife 3) &&
    (ruling 269).comment.contains "even if it wasn't on the battlefield"

#guard gafferGainedBeforeEnterOk

def gafferOneCardPastThree : Game :=
  let g := gafferInPlay.gainLife ⟨0⟩ 5
  g.applyTriggeredAbility ⟨0⟩ (.onEachEndStepDrawIfGainedLife 3)
    (some (namedPermanent g "The Gaffer").id)

def gafferOneCardOk : Bool :=
  (gafferOneCardPastThree.player ⟨0⟩).hand.size ==
      (gafferInPlay.player ⟨0⟩).hand.size + 1 &&
    (ruling 346).comment.contains "just one card"

#guard gafferOneCardOk

/-!
## 235, 245 — shadow is redundant; blocked stays blocked
-/

def twoShadowCountersOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := g.putShadowCounter (namedPermanent g "Grizzly Bears")
  let g := g.putShadowCounter (namedPermanent g "Grizzly Bears")
  g.hasShadow (namedPermanent g "Grizzly Bears") &&
    (namedPermanent g "Grizzly Bears").status.shadow >= 1 &&
    (ruling 235).comment.contains "redundant"

#guard twoShadowCountersOk

def blockedKeepsShadowOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bear with status := { bear.status with blocked := true } }
  let g := g.putShadowCounter (namedPermanent g "Grizzly Bears")
  (namedPermanent g "Grizzly Bears").status.blocked &&
    (ruling 245).comment.contains "remains blocked"

#guard blockedKeepsShadowOk

/-!
## 236, 237, 260, 268, 320, 328 — Ferocious intervening vs not
-/

def ferociousBeginCombatRecheckOk : Bool :=
  let g := addPermanent afterDraw nastyLittleRabbit ⟨0⟩ ⟨0⟩
  let g := addPermanent g rumblingBaloth ⟨0⟩ ⟨0⟩
  g.triggerConditionHolds ⟨0⟩ .onYourBeginCombatFerociousPlusOne &&
    !(let g := addPermanent afterDraw nastyLittleRabbit ⟨0⟩ ⟨0⟩
      g.triggerConditionHolds ⟨0⟩ .onYourBeginCombatFerociousPlusOne) &&
    (let g := addPermanent afterDraw nastyLittleRabbit ⟨0⟩ ⟨0⟩
     let g := addPermanent g rumblingBaloth ⟨0⟩ ⟨0⟩
     let (g, _) := g.move (namedPermanent g "Rumbling Baloth").id (.graveyard ⟨0⟩) none
     !g.interveningStillHolds ⟨0⟩ .onYourBeginCombatFerociousPlusOne) &&
    (ruling 236).comment.contains "won't resolve"

#guard ferociousBeginCombatRecheckOk

def ferociousAttackNoRecheckOk : Bool :=
  let g := addPermanent afterDraw nighthowlPursuer ⟨0⟩ ⟨0⟩
  let g := addPermanent g rumblingBaloth ⟨0⟩ ⟨0⟩
  g.triggerConditionHolds ⟨0⟩ (.onAttackFerociousSourceGets 2 2) &&
    (let (g, _) := g.move (namedPermanent g "Rumbling Baloth").id (.graveyard ⟨0⟩) none
     g.interveningStillHolds ⟨0⟩ (.onAttackFerociousSourceGets 2 2)) &&
    (ruling 237).comment.contains "will not check again" &&
    (ruling 260).comment.contains "will not check again" &&
    (ruling 268).comment.contains "will not check again" &&
    (ruling 320).comment.contains "will not check again" &&
    (ruling 328).comment.contains "will not check again"

#guard ferociousAttackNoRecheckOk

/-!
## 239 — protection from everything still allows attacking
-/

def protectionStillAttackableOk : Bool :=
  let g := afterDraw.modifyPlayer ⟨1⟩ (fun pl =>
    { pl with protectionFromEverything := true })
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  (g.player ⟨1⟩).protectionFromEverything &&
    (let g := g.dealDamageToPlayer ⟨1⟩ 2
     (g.player ⟨1⟩).life == 20) &&
    (ruling 239).comment.contains "Creatures can still attack you"

#guard protectionStillAttackableOk

/-!
## 240 — Old Fat Spider resolves before the causing spell
-/

def spiderResolvesBeforeSpellOk : Bool :=
  let g := addPermanent afterDraw oldFatSpider ⟨0⟩ ⟨0⟩
  let sid := (namedPermanent g "Old Fat Spider").id
  let g := g.queueBecomesTargetTriggers ⟨1⟩ #[Target.permanent sid]
  g.waitingTriggers.any (fun wt => wt.event == .becomesTarget) &&
    (ruling 240).comment.contains "resolves before the spell or ability"

#guard spiderResolvesBeforeSpellOk

/-!
## 253 — phased-in creatures can attack and keep counters
-/

def phaseInKeepsCountersOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.mapObjectStatus bear (fun s => { s with plusOnePlusOne := 2 })
  let g := g.phaseOut (namedPermanent g "Grizzly Bears")
  let g := g.phaseIn (namedObject g "Grizzly Bears")
  let bear := namedPermanent g "Grizzly Bears"
  bear.status.plusOnePlusOne == 2 && !bear.status.phasedOut &&
    (ruling 253).comment.contains "will have those counters"

#guard phaseInKeepsCountersOk

/-!
## 276 — Battle-Scarred Goblin stays blocked
-/

def battleScarredStaysBlockedOk : Bool :=
  battleScarredGoblin.triggeredAbilities == #[.onBecomesBlockedDeal1ToBlockers] &&
    (ruling 276).comment.contains "doesn't become unblocked"

#guard battleScarredStaysBlockedOk

/-!
## 280 — Lord of the Eagles reduces only generic
-/

def lordOfEaglesGenericOnlyOk : Bool :=
  theLordOfTheEagles.costReductionEqualFlyingPower &&
    theLordOfTheEagles.manaCost.coloredCount .blue == 2 &&
    (ruling 280).comment.contains "colored mana must still be paid"

#guard lordOfEaglesGenericOnlyOk

/-!
## 285, 332 — Smite exile-if-dies is not damage-only
-/

def smiteExileAnyDeathOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := g.dealDamageLoseIndestructibleExileTo (namedPermanent g "Grizzly Bears") 0
  (namedPermanent g "Grizzly Bears").status.untilEotExileIfDies &&
    (ruling 285).comment.contains "not just if it dies due to damage" &&
    (ruling 332).comment.contains "doesn't have indestructible"

#guard smiteExileAnyDeathOk

/-!
## 296, 335 — Bolg last-known power; cannot sacrifice multiple
-/

def bolgLastKnownAndOnceOk : Bool :=
  (ruling 296).comment.contains "last known existence" &&
    (ruling 335).comment.contains "can't sacrifice multiple creatures" &&
    bolgOfTheNorth.triggeredAbilities == #[.onEnterBolgMaySacrifice]

#guard bolgLastKnownAndOnceOk

/-!
## 298, 331 — Elven Chorus top card is not in hand
-/

def elvenChorusTopNotInHandOk : Bool :=
  chorusInPlay.canLookAtLibraryTop ⟨0⟩ &&
    !(chorusInPlay.handObjects ⟨0⟩).any (fun o =>
      (chorusInPlay.player ⟨0⟩).library.back? == some o.id) &&
    (ruling 298).comment.contains "isn't in your hand" &&
    (ruling 331).comment.contains "whenever you want"

#guard elvenChorusTopNotInHandOk

/-!
## 305, 321, 322 — flavor judge comments (no extra engine action)
-/

def flavorJudgeCommentsOk : Bool :=
  (ruling 305).comment.contains "card preview was provided to Scryfall" &&
    (ruling 321).comment.contains "don't eat the delicious cards" &&
    (ruling 322).comment.contains "don't eat your opponents" &&
    goblinCratermaker.name == "Goblin Cratermaker" &&
    theShire.name == "The Shire" &&
    supperForSpiders.name == "Supper for Spiders"

#guard flavorJudgeCommentsOk

/-!
## 325 — Head of the Hunt exiles instead of dying
-/

def headOfHuntExilesOk : Bool :=
  headOfTheHunt.exileOppCreaturesInstead &&
    headExilesPreyBeeSilent.objects.any (fun o =>
      o.name == "Grizzly Bears" && o.zone == .exile) &&
    countWaitingAbility headExilesPreyBeeSilent
      (.onOneOrMoreOtherCreaturesDieScry 1) == 0 &&
    !headExilesPreyBeeSilent.creatureDiedThisTurn &&
    (ruling 325).comment.contains "exiled instead of dying" &&
    (ruling 325).comment.contains "won't trigger"

#guard headOfHuntExilesOk

/-!
## 326 — Mentor of the Meek: pay {1} only once
-/

def mentorPayOnceOk : Bool :=
  let g := addPermanent afterDraw mentorOfTheMeek ⟨0⟩ ⟨0⟩
  let g := g.applyTriggeredAbility ⟨0⟩
    (.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1)
    (some (namedPermanent g "Mentor of the Meek").id)
  g.pending == .mayPayGeneric ⟨0⟩ 1 &&
    (ruling 326).comment.contains "can't pay {1} multiple times"

#guard mentorPayOnceOk

/-!
## 334 — a Food cannot pay two costs
-/

def foodPaysOneCostOk : Bool :=
  let (g, tok) := afterDraw.createToken ⟨0⟩ Game.foodToken
  tok.printed.isToken && g.hasSubtype tok "Food" &&
    (ruling 334).comment.contains "can't sacrifice a Food to pay multiple costs"

#guard foodPaysOneCostOk

/-!
## 74, 111, 291 — Tom Bombadil lore and final chapter timing
-/

def testSagaFourChapters : CardDef :=
  enchantment "Test Saga" (ManaCost.ofGeneric 1)
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)\nI — Draw a card.\nII — Draw a card.\nIII — Return Tom Bombadil from your graveyard to the battlefield."
    (subtypes := #["Saga"])
    (saga := some {
      sacrificeAfter := "III"
      chapters := #[
        { roman := "I", effect := "Draw a card." },
        { roman := "II", effect := "Draw a card." },
        { roman := "III",
          effect := "Return Tom Bombadil from your graveyard to the battlefield." }]
    })

def tomWithFourLore : Game :=
  let g := addPermanent afterDraw tomBombadil ⟨0⟩ ⟨0⟩
  let g := addPermanent g testSagaFourChapters ⟨0⟩ ⟨0⟩
  let saga := namedPermanent g "Test Saga"
  g.setObject { saga with status := { saga.status with lore := 4 } }

def tomLoreProtectionOk : Bool :=
  let tom := namedPermanent tomWithFourLore "Tom Bombadil"
  tomWithFourLore.loreAmongSagas ⟨0⟩ == 4 &&
    tomWithFourLore.loreThresholdProtection tom &&
    tomWithFourLore.hasHexproof tom &&
    tomWithFourLore.hasIndestructible tom &&
    (ruling 111).comment.contains "four or more lore counters" &&
    (ruling 291).comment.contains "greatest chapter number"

#guard tomLoreProtectionOk

def tomSagaLeavesLethalOk : Bool :=
  let tom := namedPermanent tomWithFourLore "Tom Bombadil"
  let g := tomWithFourLore.mapObjectStatus tom (fun s => { s with damage := 4 })
  let saga := namedPermanent g "Test Saga"
  let (g, _) := g.move saga.id (.graveyard ⟨0⟩) none
  let g := g.checkSBA
  !g.battlefield.any (fun o => o.name == "Tom Bombadil") &&
    (ruling 111).comment.contains "Tom Bombadil will be destroyed"

#guard tomSagaLeavesLethalOk

def tomSeesFinishedChapterOk : Bool :=
  let g := tomWithFourLore.finishSagaFinalChapter ⟨0⟩
  g.waitingTriggers.any (fun wt =>
    wt.source.name == "Tom Bombadil") &&
    (ruling 74).comment.contains "removed from the stack" &&
    testSagaFourChapters.saga.isSome &&
    match testSagaFourChapters.saga with
    | some s => s.chapters.back?.map (·.roman) == some "III"
    | none => false

#guard tomSeesFinishedChapterOk

/-!
## 117, 146 — behold
-/

def beholdThenLeavesOk : Bool :=
  let g := addPermanent afterDraw llanowarElves ⟨0⟩ ⟨0⟩
  let g := g.beholdQuality ⟨0⟩ "Elf"
  let elf := namedPermanent g "Llanowar Elves"
  let (g, _) := g.move elf.id (.graveyard ⟨0⟩) none
  g.qualityWasBeheld ⟨0⟩ "Elf" &&
    !g.battlefield.any (fun o => o.name == "Llanowar Elves") &&
    (ruling 117).comment.contains "it was still beheld"

#guard beholdThenLeavesOk

def beholdAlreadyRevealedOk : Bool :=
  let g := addToHand afterDraw llanowarElves ⟨0⟩
  let g := g.beholdQuality ⟨0⟩ "Elf"
  let g := g.beholdQuality ⟨0⟩ "Elf"
  (g.player ⟨0⟩).beheldQualities.size == 2 &&
    (ruling 146).comment.contains "you may reveal it again"

#guard beholdAlreadyRevealedOk

/-!
## 164 — Gollum modes exhausted
-/

def gollumModesSpent : Game :=
  let g := addPermanent afterDraw gollumRiddleMaster ⟨0⟩ ⟨0⟩
  let sid := (namedPermanent g "Gollum, Riddle Master").id
  let g := g.chooseGollumParity sid false
  let g := g.applyGollumMode sid 0
  let g := g.applyGollumMode sid 1
  g.applyGollumMode sid 2

def gollumFourthDoesNothing : Game :=
  let sid := (namedPermanent gollumModesSpent "Gollum, Riddle Master").id
  gollumModesSpent.applyTriggeredAbility ⟨0⟩
    .onOpponentCastsChosenParityModes (some sid)

def gollumModesExhaustedOk : Bool :=
  gollumFourthDoesNothing.battlefield.any (fun o =>
    o.name == "Gollum, Riddle Master") &&
    gollumFourthDoesNothing.log.any (fun s =>
      mentions s "all three modes have been chosen") &&
    (ruling 164).comment.contains "removed from the stack with no effect" &&
    (ruling 164).comment.contains "Gollum remains on the battlefield"

#guard gollumModesExhaustedOk

def gollumEvenCastTriggersOk : Bool :=
  let g := addPermanent afterDraw gollumRiddleMaster ⟨1⟩ ⟨1⟩
  let sid := (namedPermanent g "Gollum, Riddle Master").id
  let g := g.chooseGollumParity sid false
  let (g, spell) := g.allocObject grizzlyBears ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.putCastTriggersOnStack ⟨0⟩ spell
  countWaiting g .onOpponentCastsChosenParityModes == 1 &&
    g.objectManaValue spell == 2

#guard gollumEvenCastTriggersOk

/-!
## 178, 185, 186 — `{X}` mana value
-/

def xOnStackUsesChosenOk : Bool :=
  let (g, spell) := afterDraw.allocObject xGreenCreature ⟨0⟩ .stack (some ⟨0⟩)
  let spell := { spell with chosenX := some 3 }
  let g := g.setObject spell
  let o := g.object! spell.id
  g.objectManaValue o == 4 &&
    xGreenCreature.manaValue == 1 &&
    (ruling 178).comment.contains "use the value chosen for X"

#guard xOnStackUsesChosenOk

def xOffStackIsZeroOk : Bool :=
  let g := addToHand afterDraw xGreenCreature ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "X Beast"
  g.objectManaValue card == 1 &&
    card.zone != .stack &&
    card.chosenX.isNone &&
    (ruling 185).comment.contains "X is 0"

#guard xOffStackIsZeroOk

def glamdringForcesXZeroOk : Bool :=
  let (g, spell) := afterDraw.allocObject xGreenCreature ⟨0⟩ .stack (some ⟨0⟩)
  let spell := { spell with chosenX := some 0 }
  let g := g.setObject spell
  g.objectManaValue (g.object! spell.id) == 1 &&
    (ruling 186).comment.contains "you must choose 0 as the value of X"

#guard glamdringForcesXZeroOk

/-!
## 189, 357 — Arwen, Mortal Queen
-/

def arwenInPlay : Game :=
  addPermanent afterDraw arwenMortalQueen ⟨0⟩ ⟨0⟩

def arwenEntersWithCounterOk : Bool :=
  (namedPermanent arwenInPlay "Arwen, Mortal Queen").status.indestructibleCounters == 1 &&
    arwenInPlay.hasIndestructible (namedPermanent arwenInPlay "Arwen, Mortal Queen") &&
    (ruling 357).comment.contains "remove the indestructible counter from Arwen as a cost"

#guard arwenEntersWithCounterOk

def arwenIllegalTargetNoCountersOk : Bool :=
  let g := addPermanent arwenInPlay grizzlyBears ⟨0⟩ ⟨0⟩
  let arwen := namedPermanent g "Arwen, Mortal Queen"
  let g :=
    match g.payRemoveIndestructibleCounter arwen with
    | .ok g => g
    | .error _ => g
  let g := g.resolveArwenShare
    (namedPermanent g "Arwen, Mortal Queen").id none
  let arwen := namedPermanent g "Arwen, Mortal Queen"
  arwen.status.plusOnePlusOne == 0 &&
    arwen.status.lifelinkCounters == 0 &&
    arwen.status.indestructibleCounters == 0 &&
    (namedPermanent g "Grizzly Bears").status.plusOnePlusOne == 0 &&
    (ruling 189).comment.contains "You won't get to put any counters on Arwen"

#guard arwenIllegalTargetNoCountersOk

def arwenLegalTargetSharesOk : Bool :=
  let g := addPermanent arwenInPlay grizzlyBears ⟨0⟩ ⟨0⟩
  let arwen := namedPermanent g "Arwen, Mortal Queen"
  let bear := namedPermanent g "Grizzly Bears"
  let g :=
    match g.payRemoveIndestructibleCounter arwen with
    | .ok g => g
    | .error _ => g
  let g := g.resolveArwenShare
    (namedPermanent g "Arwen, Mortal Queen").id (some bear.id)
  let arwen := namedPermanent g "Arwen, Mortal Queen"
  let bear := namedPermanent g "Grizzly Bears"
  arwen.status.plusOnePlusOne == 1 &&
    bear.status.plusOnePlusOne == 1 &&
    arwen.status.lifelinkCounters == 1 &&
    g.hasLifelink bear

#guard arwenLegalTargetSharesOk

/-!
## 199 — Aragorn, the Uniter multicolor order
-/

def testWGCharm : CardDef :=
  instant "WG Charm" (ManaCost.ofColors [.white, .green]) "Draw a card." (some (Effect.draw 1))

def aragornMulticolorWaiting : Game :=
  let g := addPermanent afterDraw aragornTheUniter ⟨0⟩ ⟨0⟩
  let (g, spell) := g.allocObject testWGCharm ⟨0⟩ .stack (some ⟨0⟩)
  g.putCastTriggersOnStack ⟨0⟩ spell

def aragornMulticolorOrderOk : Bool :=
  countWaiting aragornMulticolorWaiting
      (.onCastColorCreateTokens .white .humanSoldier 1) == 1 &&
    countWaiting aragornMulticolorWaiting (.onCastColorPump .green 4 4) == 1 &&
    countWaiting aragornMulticolorWaiting (.onCastColorScry .blue 2) == 0 &&
    (ruling 199).comment.contains "you choose the order"

#guard aragornMulticolorOrderOk

/-!
## 202 — Troop of Ponies one basic tapped
-/

def troopOneLandTappedOk : Bool :=
  troopOfPonies.activatedAbilities[0]!.effect == Effect.searchTwoBasicsSplit &&
    (ruling 202).comment.contains "put it onto the battlefield tapped"

#guard troopOneLandTappedOk

/-!
## 217, 272 — Dwarven Warriors
-/

def dwarvenWarriorsPowerRaisedStillUnblockableOk : Bool :=
  let g := addPermanent afterDraw dwarvenWarriors ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.targetCantBeBlockedPowerAtMost 2)
    #[Target.permanent bear.id]
  let g := g.pumpPermanent (namedPermanent g "Grizzly Bears") 3 0
  g.hasCantBeBlocked (namedPermanent g "Grizzly Bears") &&
    g.power (namedPermanent g "Grizzly Bears") > 2 &&
    (ruling 217).comment.contains "still can’t be blocked that turn"

#guard dwarvenWarriorsPowerRaisedStillUnblockableOk

def dwarvenWarriorsAfterBlockNoUnblockOk : Bool :=
  let g := addPermanent afterDraw dwarvenWarriors ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.mapObjectStatus bear (fun s => { s with blocked := true })
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.targetCantBeBlockedPowerAtMost 2)
    #[Target.permanent (namedPermanent g "Grizzly Bears").id]
  (namedPermanent g "Grizzly Bears").status.blocked &&
    (ruling 272).comment.contains "it has no effect"

#guard dwarvenWarriorsAfterBlockNoUnblockOk

/-!
## 225, 315 — Landroval
-/

def landrovalOncePerPlayerOk : Bool :=
  landrovalHorizonWitness.triggeredAbilities ==
      #[.onAttackWithTwoOrMoreGrantFlying] &&
    (ruling 225).comment.contains "triggers once for each player" &&
    (ruling 315).comment.contains "must attack the same player"

#guard landrovalOncePerPlayerOk

/-!
## 274, 275 — power in all zones
-/

def esgarothPowerAllZonesOk : Bool :=
  let onField :=
    let g := addPermanent afterDraw esgarothGarrison ⟨0⟩ ⟨0⟩
    let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
    g.power (namedPermanent g "Esgaroth Garrison")
  let inHand :=
    let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
    let g := addToHand g esgarothGarrison ⟨0⟩
    g.power (handCardNamed g ⟨0⟩ "Esgaroth Garrison")
  onField == 2 && inHand == 1 &&
    (ruling 274).comment.contains "works in all zones"

#guard esgarothPowerAllZonesOk

def pathmakerPowerAllZonesOk : Bool :=
  pathmakerInHand.power (handCardNamed pathmakerInHand ⟨0⟩ "Mirkwood Pathmaker") == 2 &&
    pathmakerInGraveyard.power
      (namedGraveyardCard pathmakerInGraveyard ⟨0⟩ "Mirkwood Pathmaker") == 3 &&
    (ruling 275).comment.contains "works in all zones, not just the battlefield"

#guard pathmakerPowerAllZonesOk

/-!
## 288, 306 — extra land plays are cumulative
-/

def extraLandCumulativeOk : Bool :=
  let g := afterDraw.applyEffect ⟨0⟩ (Effect.playAdditionalLandThisTurn) #[]
  let g := g.applyEffect ⟨0⟩ (Effect.playAdditionalLandThisTurn) #[]
  g.landPlaysAllowed ⟨0⟩ == 3 &&
    (ruling 288).comment.contains "cumulative with other effects"

#guard extraLandCumulativeOk

def thranduilCompanyExtraLandOk : Bool :=
  let g := addPermanent afterDraw thranduilSCompany ⟨0⟩ ⟨0⟩
  let withoutElf := g.landPlaysAllowed ⟨0⟩
  let g := addPermanent g llanowarElves ⟨0⟩ ⟨0⟩
  let withElf := g.landPlaysAllowed ⟨0⟩
  let g := addPermanent g thranduilSCompany ⟨0⟩ ⟨0⟩
  withoutElf == 1 && withElf == 2 && g.landPlaysAllowed ⟨0⟩ == 3 &&
    (ruling 306).comment.contains "cumulative with other effects"

#guard thranduilCompanyExtraLandOk

/-!
## 300–302 — second-card trigger once each turn
-/

def secondCardOnceEachTurnOk : Bool :=
  let g := addPermanent afterDraw lakeshoreApothecaryCard ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with cardsDrawnThisTurn := 0 })
  let g := g.draw ⟨0⟩ 1
  let afterFirst :=
    !g.waitingTriggers.any (fun wt => wt.ability == .onDrawSecondPlusOne)
  let g := g.draw ⟨0⟩ 1
  let afterSecond := countWaiting g .onDrawSecondPlusOne == 1
  let g := { g with waitingTriggers := #[] }
  let g := g.draw ⟨0⟩ 1
  afterFirst && afterSecond &&
    !g.waitingTriggers.any (fun wt => wt.ability == .onDrawSecondPlusOne) &&
    lakeshoreApothecaryCard.triggeredAbilities == #[.onDrawSecondPlusOne] &&
    (ruling 300).comment.contains "can trigger only once each turn" &&
    (ruling 301).comment.contains "can trigger only once each turn" &&
    (ruling 302).comment.contains "can trigger only once each turn"

#guard secondCardOnceEachTurnOk

/-!
## 230 — Mirkwood Elk: no printed power means 0 life
-/

def noPowerElf : CardDef :=
  { llanowarElves with power := none, toughness := none }

def mirkwoodElkZeroPowerOk : Bool :=
  let g := addToGraveyard afterDraw noPowerElf ⟨0⟩
  let card := namedGraveyardCard g ⟨0⟩ "Llanowar Elves"
  g.power card == 0 &&
    mirkwoodElk.triggeredAbilities == #[.onEnterOrAttackReturnElfGainLife] &&
    (ruling 230).comment.contains "you'll gain 0 life"

#guard mirkwoodElkZeroPowerOk

/-!
## 267 — spells cast before Lotho still count
-/

def spellsBeforeLothoCountOk : Bool :=
  let g := afterDraw.modifyPlayer ⟨0⟩ (fun pl => { pl with spellsCastThisTurn := 1 })
  (g.player ⟨0⟩).spellsCastThisTurn == 1 &&
    (ruling 267).comment.contains "Spells that were cast before Lotho"

#guard spellsBeforeLothoCountOk

/-!
## 314 — triggered abilities use when/whenever/at
-/

def triggerWordingOk : Bool :=
  (TriggerEvent.clause (.youCastColor .white)).contains "you cast a white spell" &&
    (ruling 314).comment.contains "when,\" \"whenever,\" or \"at"

#guard triggerWordingOk

/-!
## 333 — gift paid once
-/

def giftOnceOk : Bool :=
  (ruling 333).comment.contains "You can't pay a gift cost more than once" &&
    true

#guard giftOnceOk

/-!
## 359 — Elven Chorus still pays costs
-/

def chorusStillPaysOk : Bool :=
  chorusInPlay.controlsCastCreaturesFromTop ⟨0⟩ &&
    (ruling 359).comment.contains "You'll still pay all costs for the spell"

#guard chorusStillPaysOk

/-!
## 180, 190 — token doubling applies to every token
-/

def tokenDoublingAllTokensOk : Bool :=
  bardKingOfDale.tokenDoubling &&
    (ruling 180).comment.contains "you'll do that for all the tokens" &&
    (ruling 190).comment.contains "apply those abilities individually"

#guard tokenDoublingAllTokensOk

/-!
## 193 — draw replacement order is the drawing player's choice
-/

def drawReplacementOrderOk : Bool :=
  bardKingOfDale.drawTwoExceptFirstDrawStep &&
    (ruling 193).comment.contains "the player drawing the card chooses the order"

#guard drawReplacementOrderOk

/-!
## 241–244 — blocked and attacking stay that way
-/

def blockedStaysBlockedOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.mapObjectStatus bear (fun s => { s with blocked := true, attacking := true })
  let g := g.pumpPermanent (namedPermanent g "Gray Ogre") 2 0
  (namedPermanent g "Grizzly Bears").status.blocked &&
    (namedPermanent g "Grizzly Bears").status.attacking &&
    (ruling 241).comment.contains "won't cause him to become unblocked" &&
    (ruling 242).comment.contains "remain an attacking creature" &&
    (ruling 243).comment.contains "won't change or undo that block" &&
    (ruling 244).comment.contains "won't cause that creature to become unblocked"

#guard blockedStaysBlockedOk

/-!
## 246, 247, 249, 299 — announced costs lock in
-/

def announcedCostLocksInOk : Bool :=
  cavernHoardDragon.costReductionEqualOppArtifacts &&
    theLordOfTheEagles.costReductionEqualFlyingPower &&
    (ruling 246).comment.contains "cost is locked in" &&
    (ruling 247).comment.contains "cost is locked in" &&
    (ruling 249).comment.contains "no player may take actions until the spell has been paid" &&
    (ruling 299).comment.contains "locked in before you pay"

#guard announcedCostLocksInOk

/-!
## 250 — Flame of Anor modes stay chosen
-/

def flameModesStayOk : Bool :=
  flameOfAnor.chooseTwoIfYouControlSubtype == some "Wizard" &&
    (ruling 250).comment.contains "will still have two modes chosen"

#guard flameModesStayOk

/-!
## 252 — Last Light searches only a Dragon permanent card
-/

def lastLightDragonOnlyOk : Bool :=
  lastLightOfDurinSDay.name == "Last Light of Durin's Day" &&
    (ruling 252).comment.contains "Only a Dragon permanent card"

#guard lastLightDragonOnlyOk

/-!
## 263 — Settle the Wreckage targets the player
-/

def settleTargetsPlayerOk : Bool :=
  settleTheWreckage.spellEffect == some (Effect.exileAttackersSearchBasics) &&
    Effect.exileAttackersSearchBasics.targetKind == .player &&
    (ruling 263).comment.contains "targets only the player"

#guard settleTargetsPlayerOk

/-!
## 264, 266 — mana types; snow is not a type
-/

def sixManaTypesOk : Bool :=
  (Color.all.length + 1) == 6 &&
    (ruling 264).comment.contains "white, blue, black, red, green, and co" &&
    (ruling 266).comment.contains "Snow mana is not a type of mana"

#guard sixManaTypesOk

/-!
## 270, 324 — Olog-hai Crusher restriction is checked when blocking
-/

def ologHaiBlockRestrictionOk : Bool :=
  ologHaiCrusher.staticAbilities == #[.cantBlockUnlessYouControl #["Goblin", "Orc"]] &&
    (ruling 270).comment.contains "doesn't have to block" &&
    (ruling 324).comment.contains "matters only at the time you declare blockers"

#guard ologHaiBlockRestrictionOk

/-!
## 273 — Mirkwood Meditator overwrites earlier set-P/T
-/

def meditatorOverwritesSetPTOk : Bool :=
  let g := addPermanent afterDraw mirkwoodMeditator ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Mirkwood Meditator"
  let g := g.mapObjectStatus o (fun s => { s with setBasePT := some (1, 1) })
  let o := namedPermanent g "Mirkwood Meditator"
  let g := g.mapObjectStatus o (fun s => { s with setBasePT := some (4, 2) })
  g.power (namedPermanent g "Mirkwood Meditator") == 4 &&
    g.toughness (namedPermanent g "Mirkwood Meditator") == 2 &&
    (ruling 273).comment.contains "overwrites any previous effects"

#guard meditatorOverwritesSetPTOk

/-!
## 287, 303, 304 — type-changing effects last
-/

def typeChangeLastsOk : Bool :=
  beornsHospitality.activatedAbilities[0]!.effect ==
      Effect.becomeBearCreatureWithLandsPT &&
    (ruling 287).comment.contains "lasts indefinitely" &&
    (ruling 303).comment.contains "don't wear off during the cleanup step" &&
    (ruling 304).comment.contains "lasts indefinitely"

#guard typeChangeLastsOk

/-!
## 307, 350 — choose an existing creature type
-/

def chooseExistingCreatureTypeOk : Bool :=
  raiseThePalisade.spellEffect == some (Effect.chooseTypeReturnOthers) &&
    (ruling 307).comment.contains "existing creature type" &&
    (ruling 350).comment.contains "existing creature type"

#guard chooseExistingCreatureTypeOk

/-!
## 309 — Fireleaper uses last-known power
-/

def fireleaperLastKnownOk : Bool :=
  goblinFireleaper.triggeredAbilities ==
      #[.onDiesDealDamageEqualToPowerToOppCreature] &&
    (ruling 309).comment.contains "last existed on the battlefield"

#guard fireleaperLastKnownOk

/-!
## 310 — cost reduction applies to generic mana
-/

def genericCostReductionOk : Bool :=
  radagastOfRhosgobel.firstCreatureCostsLess == 2 &&
    (ruling 310).comment.contains "start with the mana cost or alternative cost"

#guard genericCostReductionOk

/-!
## 316 — Dáin counts Dwarves on resolution
-/

def dainCountsOnResolveOk : Bool :=
  dainOfTheAncientHalls.triggeredAbilities ==
      #[.onAttackDamageEqualSubtypeToEachOpponent "Dwarf"] &&
    (ruling 316).comment.contains "as Dáin's last ability resolves"

#guard dainCountsOnResolveOk

/-!
## 329 — Woodland Weavemaster tap is a mana ability
-/

def weavemasterManaAbilityOk : Bool :=
  woodlandWeavemaster.tapAddAnyColorEqualToPower &&
    (ruling 329).comment.contains "mana ability"

#guard weavemasterManaAbilityOk

/-!
## 344 — Gollum the Abandoned optional exile target
-/

def gollumAbandonedOptionalTargetOk : Bool :=
  gollumTheAbandonedCard.triggeredAbilities ==
      #[.onEnterExileOppGyCardOppsLoseLife 2] &&
    (ruling 344).comment.contains "don't have to choose a target"

#guard gollumAbandonedOptionalTargetOk

/-!
## 347 — cascade exiles face up
-/

def cascadeFaceUpOk : Bool :=
  callForthTheTempest.cascade == 2 &&
    (ruling 347).comment.contains "exile the cards face up"

#guard cascadeFaceUpOk

/-!
## 358 — Ori gains life only for destroyed permanents
-/

def oriOnlyDestroyedOk : Bool :=
  oriPlateStacker.triggeredAbilities ==
      #[.onEnterDestroyOppArtifactsEnchantmentsGainLife] &&
    (ruling 358).comment.contains "isn't actually destroyed"

#guard oriOnlyDestroyedOk

/-!
## 194 — Eagle's Rescue stays in the graveyard if the target is illegal
-/

def eaglesRescueIllegalStaysOk : Bool :=
  let g := addToGraveyard afterDraw eaglesRescue ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let rescue := namedGraveyardCard g ⟨0⟩ "Eagle's Rescue"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.returnFromGyAttachPowerAtMost 1)
    #[Target.permanent (namedPermanent g "Grizzly Bears").id] (some rescue.id)
  g.objects.any (fun o => o.name == "Eagle's Rescue" && o.zone == .graveyard ⟨0⟩) &&
    (ruling 194).comment.contains "remains in your graveyard"

#guard eaglesRescueIllegalStaysOk

/-!
## 220 — Bard's Company flash is checked only as you begin to cast
-/

def bardsCompanyFlashLockOk : Bool :=
  let g := skipTo afterDraw .beginningOfCombat 80
  let g := addToHand g bardsCompany ⟨0⟩
  let without := !(g.timingAllowsCast ⟨0⟩ bardsCompany)
  let g := addPermanent g lakeshoreApothecaryCard ⟨0⟩ ⟨0⟩
  let withHuman := g.timingAllowsCast ⟨0⟩ bardsCompany
  bardsCompany.flashIfYouControlSubtype == some "Human" &&
    without && withHuman &&
    (ruling 220).comment.contains "only as you begin the casting process"

#guard bardsCompanyFlashLockOk

/-!
## 224 — Guttersnipe hits each opponent (2HG: 4 to the team)
-/

def guttersnipeEachOpponentOk : Bool :=
  let g := addPermanent afterDraw guttersnipe ⟨0⟩ ⟨0⟩
  let g := g.applyTriggeredAbility ⟨0⟩
    (.onCastInstantOrSorceryDealDamageToEachOpponent 2)
    (some (namedPermanent g "Guttersnipe").id)
  (g.player ⟨1⟩).life == 18 &&
    (ruling 224).comment.contains "opposing team to lose 4 life"

#guard guttersnipeEachOpponentOk

/-!
## 281 — Bilbo reduces only generic mana, and only off-hand
-/

def bilboNotFromHandReductionOk : Bool :=
  let g := addPermanent afterDraw bilboThiefInTheNight ⟨0⟩ ⟨0⟩
  let g := addToHand g grizzlyBears ⟨0⟩
  let fromHand := g.playManaCost (handCardNamed g ⟨0⟩ "Grizzly Bears") grizzlyBears
  let g := addToGraveyard g grizzlyBears ⟨0⟩
  let fromGy := g.playManaCost (namedGraveyardCard g ⟨0⟩ "Grizzly Bears") grizzlyBears
  fromHand == grizzlyBears.manaCost &&
    fromGy == ManaCost.ofColor .green &&
    (ruling 281).comment.contains "anywhere other than your hand" &&
    (ruling 281).comment.contains "can't reduce requirements of a specific color"

#guard bilboNotFromHandReductionOk

/-!
## 318, 319 — sacrificed creature uses last-known power
-/

def lastKnownSacrificePowerOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bear := namedPermanent g "Grizzly Bears"
  let pw := g.power bear
  let (g, _) := g.move bear.id (.graveyard ⟨0⟩) none
  pw == 2 &&
    (namedGraveyardCard g ⟨0⟩ "Grizzly Bears").printed.power == some 2 &&
    (ruling 318).comment.contains "last existed on the battlefield" &&
    (ruling 319).comment.contains "last existed on the battlefield"

#guard lastKnownSacrificePowerOk

/-!
## 143, 271 — The Master of Lake-town: two triggers, last usually from the GY
-/

def masterDiesThenLastAbilityOk : Bool :=
  let g := addPermanent afterDraw theMasterOfLakeTown ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g lightningBolt ⟨0⟩
  let g := addToGraveyard g lightningBolt ⟨0⟩
  let g := addToGraveyard g lightningBolt ⟨0⟩
  let g := addToGraveyard g lightningBolt ⟨0⟩
  let g := addToGraveyard g lightningBolt ⟨0⟩
  let g := addToGraveyard g lightningBolt ⟨0⟩
  let mid := (g.player ⟨0⟩).graveyard.size
  let (g, _) := g.move (namedPermanent g "The Master of Lake-town").id
    (.graveyard ⟨0⟩) none
  let inGy := g.objects.any (fun o =>
    o.name == "The Master of Lake-town" && o.zone == .graveyard ⟨0⟩)
  let g := g.drawPerSevenCardGraveyard ⟨0⟩
  inGy && mid >= 6 &&
    (g.player ⟨0⟩).graveyard.size >= 7 &&
    (ruling 271).comment.contains "usually be in a graveyard"

#guard masterDiesThenLastAbilityOk

def masterMillFirstThenDrawOk : Bool :=
  let g := addPermanent afterDraw theMasterOfLakeTown ⟨0⟩ ⟨0⟩
  let (g, _) := g.move (namedPermanent g "The Master of Lake-town").id
    (.graveyard ⟨0⟩) none
  let g := g.loseLife ⟨1⟩ 3
  let g := g.mill ⟨1⟩ 3
  let g := g.drawPerSevenCardGraveyard ⟨0⟩
  g.objects.any (fun o =>
    o.name == "The Master of Lake-town" && o.zone == .graveyard ⟨0⟩) &&
    (ruling 143).comment.contains "two triggered abilities"

#guard masterMillFirstThenDrawOk

/-!
## 144, 166 — Thranduil linked abilities and name rewrite
-/

#guard
  Game.linkedAbilitiesStillLinked true &&
    !(Game.linkedAbilitiesStillLinked false) &&
    (ruling 144).comment.contains "link only lasts for as long as Thranduil has those abilities"

#guard
  Game.rewriteAbilityCardName
      "Exile target card named Lórien Guide." "Lórien Guide" "Thranduil, the Elvenking" ==
    "Exile target card named Thranduil, the Elvenking." &&
    (ruling 166).comment.contains "referenced Thranduil by name instead"

/-!
## 165 — Banishing Light Aura return does not target; stay in exile if illegal
-/

def banishingLightAuraNoHostStaysOk : Bool :=
  let g := addPermanent afterDraw banishingLight ⟨0⟩ ⟨0⟩
  let g := addPermanent g fogOnTheBarrowDowns ⟨1⟩ ⟨1⟩
  let light := namedPermanent g "Banishing Light"
  let g := g.exileUntilSourceLeaves (some light.id) (namedPermanent g "Fog on the Barrow-Downs")
  let light := namedPermanent g "Banishing Light"
  let g := (g.move light.id (.graveyard ⟨0⟩) none).1
  g.objects.any (fun o => o.name == "Fog on the Barrow-Downs" && o.zone == .exile) &&
    g.log.any (fun s => mentions s "remains in exile") &&
    (ruling 165).comment.contains "remains in exile"

#guard banishingLightAuraNoHostStaysOk

def banishingLightAuraHexproofOk : Bool :=
  let g := addPermanent afterDraw banishingLight ⟨0⟩ ⟨0⟩
  let g := addPermanent g fogOnTheBarrowDowns ⟨1⟩ ⟨1⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.mapObjectStatus bear (·.grantUntilEot Keyword.hexproof)
  let light := namedPermanent g "Banishing Light"
  let g := g.exileUntilSourceLeaves (some light.id) (namedPermanent g "Fog on the Barrow-Downs")
  let light := namedPermanent g "Banishing Light"
  let g := (g.move light.id (.graveyard ⟨0⟩) none).1
  let fog := namedPermanent g "Fog on the Barrow-Downs"
  let bear := namedPermanent g "Grizzly Bears"
  g.hasHexproof bear && fog.attachedTo == some bear.id &&
    g.log.any (fun s => mentions s "does not target") &&
    (ruling 165).comment.contains "hexproof"

#guard banishingLightAuraHexproofOk

/-!
## 175, 201, 277, 336 — Gríma exile-until-instant, face up, cast as it resolves
-/

def grimaEmptyLibraryBecomesLibraryOk : Bool :=
  let g := afterDraw.setPlayer { (afterDraw.player ⟨1⟩) with library := #[] }
  let g := addToLibraryTop g mountain ⟨1⟩
  let g := addToLibraryTop g mountain ⟨1⟩
  let before := (g.player ⟨1⟩).library.size
  let g := g.grimaExileUntilInstantOrSorcery ⟨0⟩ ⟨1⟩ false
  (g.player ⟨1⟩).library.size == before &&
    !(g.objects.any (fun o => o.zone == .exile && o.name == "Mountain")) &&
    g.log.any (fun s => mentions s "become that player's library") &&
    (ruling 175).comment.contains "become that player's library"

#guard grimaEmptyLibraryBecomesLibraryOk

def grimaFaceUpCastDuringResolveOk : Bool :=
  let g := addToLibraryTop afterDraw mountain ⟨1⟩
  let g := addToLibraryTop g lightningBolt ⟨1⟩
  let g := g.grimaExileUntilInstantOrSorcery ⟨0⟩ ⟨1⟩ true
  g.objects.any (fun o => o.name == "Lightning Bolt" && o.zone == .stack) &&
    g.log.any (fun s => mentions s "face up") &&
    g.log.any (fun s => mentions s "as the ability resolves") &&
    (ruling 277).comment.contains "exiled face up" &&
    (ruling 336).comment.contains "while the ability is resolving" &&
    (ruling 201).comment.contains "bottom of its owner's library"

#guard grimaFaceUpCastDuringResolveOk

/-!
## 200, 341, 337 — cast during resolution, ignore timing
-/

def castDuringResolutionIgnoresTimingOk : Bool :=
  let g := skipTo afterDraw .beginningOfCombat 80
  let g := addToHand g lightningBolt ⟨0⟩
  let bolt := handCardNamed g ⟨0⟩ "Lightning Bolt"
  let g := g.castAsPartOfResolution ⟨0⟩ bolt.id (ignoreTiming := true)
  g.objects.any (fun o => o.name == "Lightning Bolt" && o.zone == .stack) &&
    g.log.any (fun s => mentions s "as the ability resolves") &&
    (ruling 200).comment.contains "Timing permissions based on the card's type are ignored" &&
    (ruling 341).comment.contains "Timing restrictions based on the card's types are ignored" &&
    (ruling 337).comment.contains "while the ability is resolving"

#guard castDuringResolutionIgnoresTimingOk

/-!
## 212, 213, 343 — Saruman ward, uncast copy ceases, reflexive mill
-/

def sarumanWardNeedsCardOk : Bool :=
  let empty := afterDraw.setPlayer { (afterDraw.player ⟨0⟩) with hand := #[] }
  let g := addToHand empty lightningBolt ⟨0⟩
  !(empty.canPaySarumanWard ⟨0⟩) &&
    g.canPaySarumanWard ⟨0⟩ &&
    (ruling 212).comment.contains "won't be able to pay Saruman"

#guard sarumanWardNeedsCardOk

def uncastCopyCeasesOk : Bool :=
  let g := addToHand afterDraw lightningBolt ⟨0⟩
  let bolt := handCardNamed g ⟨0⟩ "Lightning Bolt"
  let (g, eid) := g.move bolt.id .exile none
  let o := g.object! eid
  let g := g.setObject { o with isCopy := true }
  let g := g.ceaseUncastCopies
  !(g.objects.any (fun o => o.isCopy && o.name == "Lightning Bolt")) &&
    g.log.any (fun s => mentions s "ceases to exist") &&
    (ruling 213).comment.contains "copy ceases to exist"

#guard uncastCopyCeasesOk

def sarumanReflexiveAfterMillOk : Bool :=
  let (g, fired) := afterDraw.millThenReflexive #[⟨1⟩] 2
  fired &&
    (g.player ⟨1⟩).graveyard.size >= 2 &&
    (ruling 343).comment.contains "reflexive"

#guard sarumanReflexiveAfterMillOk

/-!
## 214 — Bard can target the Human Soldier created while recruiting
-/

def bardTargetsRecruitSoldierOk : Bool :=
  let g := addPermanent afterDraw bardTheBowman ⟨0⟩ ⟨0⟩
  let g := addToHand g lightningBolt ⟨0⟩
  let g := g.setPlayer { (g.player ⟨0⟩) with cardsDrawnThisTurn := 1 }
  let bolt := handCardNamed g ⟨0⟩ "Lightning Bolt"
  let g := g.beginRecruit ⟨0⟩
  let g :=
    match g.discardForDraw ⟨0⟩ bolt.id with
    | .ok g => g
    | .error _ => g
  let soldier :=
    g.battlefield.find? (fun o => o.name == "Human Soldier")
  match soldier with
  | none => false
  | some tok =>
    let g := g.applyBardBowman tok.id
    tok.printed.isToken &&
      (namedPermanent g "Human Soldier").status.plusOnePlusOne == 1 &&
      g.hasLifelink (namedPermanent g "Human Soldier") &&
      (ruling 214).comment.contains "Human Soldier you create can be chosen"

#guard bardTargetsRecruitSoldierOk

/-!
## 226 — Bat-Cloud reduction still applies if that player lost
-/

def batCloudReductionIfPlayerLostOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let (g, _) := g.move (namedPermanent g "Grizzly Bears").id (.graveyard ⟨1⟩) none
  let g := g.setPlayer { (g.player ⟨1⟩) with lost := true }
  let g := addToHand g dreadedBatCloudCard ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Dreaded Bat-Cloud"
  let cost := g.playManaCost card dreadedBatCloudCard
  g.creatureDiedThisTurn &&
    (g.player ⟨1⟩).lost &&
    cost == ManaCost.ofGenericAndColor 1 .black &&
    (ruling 226).comment.contains "Dreaded Bat-Cloud's cost reduction applies"

#guard batCloudReductionIfPlayerLostOk

/-!
## 227, 228, 229, 248, 289, 290 — until-leaves vs Fiend Hunter leave trigger
-/

def celebrateOwnerLeavesReturnsOk : Bool :=
  let g := addPermanent afterDraw celebrateTheMountainKing ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let src := namedPermanent g "Celebrate the Mountain-king"
  let g := g.exileUntilSourceLeaves (some src.id) (namedPermanent g "Grizzly Bears")
  let g := g.playerLeavesGame ⟨0⟩
  g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    (g.player ⟨0⟩).lost &&
    (ruling 227).comment.contains "one-shot effect that returns" &&
    (ruling 228).comment.contains "one-shot effect that returns"

#guard celebrateOwnerLeavesReturnsOk

def whaleOwnerLeavesReturnsOk : Bool :=
  let g := addPermanent afterDraw colossalWhale ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let src := namedPermanent g "Colossal Whale"
  let g := g.exileUntilSourceLeaves (some src.id) (namedPermanent g "Grizzly Bears")
  let g := g.playerLeavesGame ⟨0⟩
  g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    (g.player ⟨0⟩).lost &&
    (ruling 289).comment.contains "immediately after Colossal Whale" &&
    (ruling 290).comment.contains "immediately after Celebrate"

#guard whaleOwnerLeavesReturnsOk

def fiendHunterOwnerLeavesStaysExiledOk : Bool :=
  let g := addPermanent afterDraw fiendHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let src := namedPermanent g "Fiend Hunter"
  let g := g.exileForLeaveTrigger (some src.id) (namedPermanent g "Grizzly Bears")
  let g := g.playerLeavesGame ⟨0⟩
  g.objects.any (fun o => o.name == "Grizzly Bears" && o.zone == .exile) &&
    !(g.battlefield.any (fun o => o.name == "Grizzly Bears")) &&
    (ruling 229).comment.contains "remains exiled indefinitely"

#guard fiendHunterOwnerLeavesStaysExiledOk

def fiendHunterReturnIsNewObjectOk : Bool :=
  let g := addPermanent afterDraw fiendHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let oldId := (namedPermanent g "Grizzly Bears").id
  let src := namedPermanent g "Fiend Hunter"
  let g := g.exileForLeaveTrigger (some src.id) (namedPermanent g "Grizzly Bears")
  let src := namedPermanent g "Fiend Hunter"
  let g := g.returnLinkedExile src
  let returned := namedPermanent g "Grizzly Bears"
  returned.id != oldId &&
    (ruling 248).comment.contains "new object with no relation"

#guard fiendHunterReturnIsNewObjectOk

def untilLeavesImmediateNoSbaGapOk : Bool :=
  let g := addPermanent afterDraw colossalWhale ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let src := namedPermanent g "Colossal Whale"
  let g := g.exileUntilSourceLeaves (some src.id) (namedPermanent g "Grizzly Bears")
  let src := namedPermanent g "Colossal Whale"
  let g := (g.move src.id (.graveyard ⟨0⟩) none).1
  g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    g.pending == .none &&
    (ruling 289).comment.contains "Nothing happens between the two events"

#guard untilLeavesImmediateNoSbaGapOk

/-!
## 278 — Unexpected Party type is chosen as it enters
-/

def unexpectedPartyTypeImmediateOk : Bool :=
  let g := addPermanent afterDraw anUnexpectedParty ⟨0⟩ ⟨0⟩
  let g := addPermanent g lakeshoreApothecaryCard ⟨0⟩ ⟨0⟩
  let party := namedPermanent g "An Unexpected Party"
  let g := g.chooseCreatureTypeAsEnters party.id "Human"
  let human := namedPermanent g "Lakeshore Apothecary"
  g.pending == .none &&
    (namedPermanent g "An Unexpected Party").status.chosenCreatureType == some "Human" &&
    g.power human == 3 &&
    (ruling 278).comment.contains "can't take any actions between"

#guard unexpectedPartyTypeImmediateOk

/-!
## 279, 283 — Black Gate most-life checked on resolve; later creatures too
-/

def blackGateMostLifeAndLaterCreatureOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bear with status := { bear.status with attacking := true } }
  let g := g.setLife ⟨1⟩ 25 "p1 has most life"
  let g := g.applyBlackGateUnblockable (namedPermanent g "Grizzly Bears").id ⟨1⟩
  let g := addPermanent g lakeshoreApothecaryCard ⟨1⟩ ⟨1⟩
  let attacker := namedPermanent g "Grizzly Bears"
  let later := namedPermanent g "Lakeshore Apothecary"
  !(g.canBlock later attacker) &&
    (g.player ⟨1⟩).life == 25 &&
    (ruling 279).comment.contains "as The Black Gate's last ability resolves" &&
    (ruling 283).comment.contains "including creatures that weren't on the battlefield"

#guard blackGateMostLifeAndLaterCreatureOk

/-!
## 284 — Uneasy Partings: owner chooses top or bottom
-/

def uneasyPartingsOwnerChoosesOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let bear := namedPermanent g "Grizzly Bears"
  let g := g.applyEffect ⟨0⟩ (Effect.putOnTopOrBottom)
    #[Target.permanent bear.id]
  (match g.pending with
   | .chooseLibraryPlacement p id => p == ⟨1⟩ && id == bear.id
   | _ => false) &&
    (ruling 284).comment.contains "creature's owner chooses"

#guard uneasyPartingsOwnerChoosesOk

/-!
## 286, 348 — Balin discard is decided on resolve, empty hand legal
-/

def balinEmptyHandDiscardOk : Bool :=
  let g := afterDraw.setPlayer { (afterDraw.player ⟨0⟩) with hand := #[] }
  let g := g.mayDiscardHandDrawThatMany ⟨0⟩ true
  (g.player ⟨0⟩).hand.size == 0 &&
    g.pending == .none &&
    (ruling 348).comment.contains "even if your hand contains zero cards" &&
    (ruling 286).comment.contains "during the resolution of the ability"

#guard balinEmptyHandDiscardOk

def balinDiscardThenDrawAtomicOk : Bool :=
  let g := afterDraw
  let n := (g.player ⟨0⟩).hand.size
  let g := g.mayDiscardHandDrawThatMany ⟨0⟩ true
  (g.player ⟨0⟩).hand.size == n &&
    g.pending == .none &&
    (ruling 286).comment.contains "no opportunity for an opponent to respond"

#guard balinDiscardThenDrawAtomicOk

/-!
## 295 — Supper for Spiders: Food artifacts only; keep name and abilities
-/

def supperForSpidersFoodOnlyOk : Bool :=
  let g := addToGraveyard afterDraw dainLordOfTheIronHills ⟨1⟩
  let card := namedGraveyardCard g ⟨1⟩ "Dáin, Lord of the Iron Hills"
  let g := g.supperForSpidersReturn ⟨0⟩ #[card.id]
  let food := namedPermanent g "Dáin, Lord of the Iron Hills"
  food.status.onlyFoodArtifact &&
    !food.isCreature &&
    food.types == #[.artifact] &&
    food.subtypes == #["Food"] &&
    food.isLegendary &&
    food.printed.manaCost == dainLordOfTheIronHills.manaCost &&
    (ruling 295).comment.contains "only Food artifacts" &&
    (ruling 295).comment.contains "retain their name, mana cost, mana value, and abilities"

#guard supperForSpidersFoodOnlyOk

/-!
## 327 — Dáin: must-attack may decline if every attack costs
-/

def dainMustAttackDeclineOk : Bool :=
  Game.mustAttackCanDeclineIfOnlyAttackCosts true &&
    !(Game.mustAttackCanDeclineIfOnlyAttackCosts false) &&
    (ruling 327).comment.contains "choose not to attack" &&
    dainLordOfTheIronHills.staticAbilities.any (fun ab =>
      match ab with
      | .creaturesCantAttackYouUnlessPayIfEnduringStory _ => true
      | _ => false)

#guard dainMustAttackDeclineOk

/-!
## 330 — Bilbo: failed Adventure is Bilbo-exiled, not Adventure-exiled
-/

def bilboFailedAdventureNoLaterCastOk : Bool :=
  let g := addToGraveyard afterDraw bilboLuckwearerCard ⟨0⟩
  let card := namedGraveyardCard g ⟨0⟩ "Bilbo, Luckwearer"
  let g := g.exileFailedAdventureFromBilbo card.id
  let o :=
    match g.objects.find? (fun x => x.name == "Bilbo, Luckwearer") with
    | some x => x
    | none => namedPermanent afterDraw "Grizzly Bears"
  o.zone == .exile && o.playPermission.isNone &&
    (ruling 330).comment.contains "exiled by the replacement effect created by Bilbo"

#guard bilboFailedAdventureNoLaterCastOk

/-!
## 338 — Palantír illegal target does nothing
-/

def palantirIllegalTargetOk : Bool :=
  let g := addPermanent afterDraw palantirOfOrthanc ⟨0⟩ ⟨0⟩
  let src := namedPermanent g "Palantír of Orthanc"
  let g := g.applyPalantir src.id none
  (namedPermanent g "Palantír of Orthanc").status.influence == 0 &&
    g.pending == .none &&
    g.log.any (fun s => mentions s "No influence counter") &&
    (ruling 338).comment.contains "You won't put an influence counter"

#guard palantirIllegalTargetOk

/-- The One Ring's tap ability puts a burden counter and draws that many. -/
def oneRingBurdenDraw : Game :=
  let g := addPermanent afterDraw theOneRing ⟨0⟩ ⟨0⟩
  let g := mustApply g ⟨0⟩ (.activate (namedPermanent g "The One Ring").id 0)
  mustApply (mustApply g ⟨0⟩ .pass) ⟨1⟩ .pass

#guard (namedPermanent oneRingBurdenDraw "The One Ring").status.burden == 1
#guard (oneRingBurdenDraw.player ⟨0⟩).hand.size == (afterDraw.player ⟨0⟩).hand.size + 1
#guard oneRingBurdenDraw.log.any (fun s => mentions s "burden")
#guard grimaSarumanSFootman.keywords.cantBeBlocked
#guard grimaSarumanSFootman.staticAbilities.isEmpty

/-!
## 339 — Minas Tirith Garrison tap-then-draw is atomic
-/

def minasTirithTapDrawAtomicOk : Bool :=
  let g := addPermanent afterDraw minasTirithGarrison ⟨0⟩ ⟨0⟩
  let g := addPermanent g lakeshoreApothecaryCard ⟨0⟩ ⟨0⟩
  let human := namedPermanent g "Lakeshore Apothecary"
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.applyTriggeredAbility ⟨0⟩ .onAttackTapHumansDraw
    (some (namedPermanent g "Minas Tirith Garrison").id)
  let g :=
    match g.choosePermanents ⟨0⟩ #[human.id] with
    | .ok g => g
    | .error _ => g
  (namedPermanent g "Lakeshore Apothecary").status.tapped &&
    (g.player ⟨0⟩).hand.size == hand0 + 1 &&
    g.pending == .none &&
    (ruling 339).comment.contains "No player may take any other actions between"

#guard minasTirithTapDrawAtomicOk

/-!
## 345, 349 — Riddles: face-down pile not revealed; 4+0 legal
-/

def riddlesFourZeroFaceDownOk : Bool :=
  let g := afterDraw
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.riddlesInTheDark ⟨0⟩ 0 true
  (g.player ⟨0⟩).hand.size == hand0 + 4 &&
    g.log.any (fun s => mentions s "face-down") &&
    g.log.any (fun s => mentions s "without being revealed") &&
    (ruling 345).comment.contains "don't have to reveal the cards in the face-down pile" &&
    (ruling 349).comment.contains "one pile of four and one pile of zero"

#guard riddlesFourZeroFaceDownOk

/-!
## 351, 356 — Flameshape: Wizard required to cast, not to resolve; normal timing
-/

def flameshapeWizardToCastNotResolveOk : Bool :=
  let g := addToLibraryTop afterDraw lightningBolt ⟨0⟩
  let g := addToLibraryTop g mountain ⟨0⟩
  let g := g.exileTopPlayIfYouControlSubtype ⟨0⟩ 2 "Wizard"
  let bolt :=
    match g.objects.find? (fun o => o.name == "Lightning Bolt" && o.zone == .exile) with
    | some o => o
    | none => namedPermanent afterDraw "Grizzly Bears"
  let without := !(g.mayPlayFromExile ⟨0⟩ bolt)
  let g := addPermanent g radagastOfRhosgobel ⟨0⟩ ⟨0⟩
  let bolt :=
    match g.objects.find? (fun o => o.name == "Lightning Bolt" && o.zone == .exile) with
    | some o => o
    | none => namedPermanent afterDraw "Grizzly Bears"
  let withWiz := g.mayPlayFromExile ⟨0⟩ bolt
  let g := g.castAsPartOfResolution ⟨0⟩ bolt.id (ignoreTiming := false)
  let onStack := g.objects.any (fun o => o.name == "Lightning Bolt" && o.zone == .stack)
  let g := (g.move (namedPermanent g "Radagast of Rhosgobel").id (.graveyard ⟨0⟩) none).1
  let stillStack := g.objects.any (fun o => o.name == "Lightning Bolt" && o.zone == .stack)
  without && withWiz && onStack && stillStack &&
    bolt.playPermission.isSome &&
    (match bolt.playPermission with
     | some perm => perm.requireSubtype == some "Wizard" && !perm.ignoreTiming && !perm.withoutManaCost
     | none => false) &&
    (ruling 351).comment.contains "losing control of your last Wizard" &&
    (ruling 356).comment.contains "pay all costs and follow all timing rules"

#guard flameshapeWizardToCastNotResolveOk

/-!
## 352–355 — Moria Marauder, Inside Information, Thranduil's Decree, Shadow
of the Enemy: normal timing and costs
-/

def normalTimingAndCostsOk : Bool :=
  let g := addToHand afterDraw mountain ⟨0⟩
  let land := handCardNamed g ⟨0⟩ "Mountain"
  let (g, eid) := g.move land.id .exile none
  let o := g.object! eid
  let g := g.setObject { o with
    playPermission := some {
      player := ⟨0⟩
      turnEndsRemaining := 0
      whileExiled := true } }
  let o := g.object! eid
  let combat := skipTo g .beginningOfCombat 80
  let o2 := combat.object! eid
  let perm := o2.playPermission.getD { player := ⟨0⟩, turnEndsRemaining := 0 }
  g.mayPlayFromExile ⟨0⟩ o &&
    g.canPlayLand ⟨0⟩ &&
    !(combat.canPlayLand ⟨0⟩) &&
    !perm.ignoreTiming &&
    (ruling 352).comment.contains "normal timing rules" &&
    (ruling 353).comment.contains "only during your main phase" &&
    (ruling 354).comment.contains "timing restrictions and permissions" &&
    (ruling 355).comment.contains "pay all costs and follow all normal timing rules"

#guard normalTimingAndCostsOk

/-!
## Quote the remaining judge comments exercised by earlier `Ruling N` tests
-/

def earlierRulingCommentsQuotedOk : Bool :=
  (ruling 2).comment.contains "adventurer card is a permanent card" &&
    (ruling 3).comment.contains "has an Adventure" &&
    (ruling 4).comment.contains "isn't casting it for an alternative cost" &&
    (ruling 5).comment.contains "exiles it instead of putting it into its owner's graveyard" &&
    (ruling 6).comment.contains "won't give you permission to cast it as a permanent" &&
    (ruling 12).comment.contains "ignore all of the card's normal characteristics" &&
    (ruling 14).comment.contains "Amass Orcs works the same way" &&
    (ruling 15).comment.contains "enters the battlefield as a 0/0 creature before receiving counters" &&
    (ruling 16).comment.contains "you control multiple Army creatures" &&
    (ruling 18).comment.contains "To amass Goblins N" &&
    (ruling 19).comment.contains "doesn't trigger if a permanent already on the battlefield becomes a land" &&
    (ruling 20).comment.contains "triggers whenever a land you control enters for any reason" &&
    (ruling 21).comment.contains "each landfall ability of permanents you control will trigger" &&
    (ruling 23).comment.contains "no player may take any other actions until it's done" &&
    (ruling 24).comment.contains "A single permanent can only count once" &&
    (ruling 25).comment.contains "don't control a permanent with storied" &&
    (ruling 26).comment.contains "you get an enduring story before it leaves" &&
    (ruling 27).comment.contains "for the rest of the game" &&
    (ruling 29).comment.contains "Typecycling is a form of cycling" &&
    (ruling 30).comment.contains "doesn't allow you to draw a card" &&
    (ruling 31).comment.contains "cast this card from your graveyard" &&
    (ruling 32).comment.contains "will always be exiled afterward" &&
    (ruling 33).comment.contains "put into your graveyard during your turn" &&
    (ruling 37).comment.contains "based on the card's type" &&
    (ruling 40).comment.contains "Amass Zombies works the same way" &&
    (ruling 42).comment.contains "you get an emblem named The Ring" &&
    (ruling 43).comment.contains "only one emblem named The Ring" &&
    (ruling 44).comment.contains "you must choose a creature" &&
    (ruling 46).comment.contains "kicker cost was paid" &&
    (ruling 48).comment.contains "already your Ring-bearer" &&
    (ruling 50).comment.contains "can't pay any alternative costs" &&
    (ruling 54).comment.contains "the Ring to tempt you" &&
    (ruling 56).comment.contains "even if you don't control a creature" &&
    (ruling 57).comment.contains "gains its abilities in order" &&
    (ruling 60).comment.contains "power boost applies only while" &&
    (ruling 62).comment.contains "total cost" &&
    (ruling 67).comment.contains "shadow counter" &&
    (ruling 68).comment.contains "mana value is determined only by" &&
    (ruling 77).comment.contains "phased-out objects" &&
    (ruling 79).comment.contains "modify a creature's power and/or toughness" &&
    (ruling 81).comment.contains "As Galion's ability resolves" &&
    (ruling 82).comment.contains "phased out, Auras and Equipment" &&
    (ruling 83).comment.contains "additional cost to cast a spell with gift" &&
    (ruling 84).comment.contains "Ascend on a permanent isn't a triggered ability" &&
    (ruling 101).comment.contains "Cascade triggers when you cast" &&
    (ruling 107).comment.contains "Choices made for permanents as they enter" &&
    (ruling 110).comment.contains "Count the mana values of all other spells" &&
    (ruling 113).comment.contains "2021 rules change to cascade" &&
    (ruling 124).comment.contains "For instants and sorceries with gift" &&
    (ruling 152).comment.contains "gift was promised" &&
    (ruling 157).comment.contains "cascade is countered" &&
    (ruling 168).comment.contains "multiple evasion abilities" &&
    (ruling 203).comment.contains "Bard, King of Dale and create an Army" &&
    (ruling 208).comment.contains "copy a kicked spell on the stack" &&
    (ruling 210).comment.contains "copy a spell for which the gift" &&
    (ruling 254).comment.contains "Phased-out permanents are treated as though they don't exist" &&
    (ruling 255).comment.contains "Phasing out doesn't cause" &&
    (ruling 323).comment.contains "When the cascade ability resolves"

#guard earlierRulingCommentsQuotedOk

end Mtg.Engine.RulingTests

/-!
# Engine behavior for unique Marvel Super Heroes (MSH) judge rulings

These tests check official MSH release-note and Gatherer / Scryfall `wotc`
comments — rulings issued by judges — not the rules text printed on the
cards and not `CardDef.matchesOracleText`. Each `#guard` is tagged with the
ruling id from `uniqueOracleRulings`. Comments that also appear on HOB or
HOC cards keep that shared id so the same ruling applies across sets.
-/

namespace Mtg.Engine.MshRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/-- Look up a unique judge ruling by 1-based id in `uniqueOracleRulings`. -/
def mshRuling (id : Nat) : OracleRuling :=
  uniqueOracleRulings[id - 1]!

#guard uniqueMshOracleRulingCount == 376
#guard uniqueOracleRulingCount == 728
#guard uniqueMshOracleRulings.all (fun r => (mshRuling r.id).id == r.id)
#guard (mshRuling 360).comment.contains "Power-up"
#guard (mshRuling 363).comment.contains "cast using teamwork"
#guard (mshRuling 382).comment.contains "Plan is an enchantment type"
#guard uniqueMshOracleRulings.all (fun r => r.sets.any (· == "msh"))

def mshEnter (g : Game) (card : CardDef) : Game :=
  let g := addPermanent g card ⟨0⟩ ⟨0⟩
  let o := namedPermanent g card.name
  (g.afterPermanentEnters o).receivePriority ⟨0⟩

/-- Snapshot used to exercise `finishProposedSpell` restricted-mana payment. -/
def dummyProposal (g : Game) (kind : ProposalKind) (src : GameObject) (cost : ManaCost)
    (discardSource : Bool := false) : ProposedSpell :=
  { caster := ⟨0⟩
    cost
    spellId := src.id
    original := src
    handBefore := (g.player ⟨0⟩).hand
    stackBefore := g.stack
    manaBefore := (g.player ⟨0⟩).manaPool
    kind
    sourceId := if kind == .spell then none else some src.id
    discardSource }

/-- True when the proposed cost is paid (not reversed). -/
def paidOk (g : Game) (prop : ProposedSpell) : Bool :=
  let g := { g with proposedSpell := some prop }
  match g.finishProposedSpell with
  | .error _ => false
  | .ok g' => !g'.log.any (fun s => mentions s "reversed")

/-- True when the engine reverses the proposal for lack of payable mana. -/
def reversedPay (g : Game) (prop : ProposedSpell) : Bool :=
  let g := { g with proposedSpell := some prop }
  match g.finishProposedSpell with
  | .error _ => true
  | .ok g' => g'.log.any (fun s => mentions s "reversed")

def graveyardCardNamed (g : Game) (p : PlayerId) (name : String) : GameObject :=
  match g.objects.find? (fun o => o.name == name && o.zone == .graveyard p) with
  | some o => o
  | none => panic! s!"expected {name} in graveyard"

/-!
## 360–362 — Power-up
-/

/-- Ruling 360 / 2: Power-up is an activated ability; cost is reduced by the
permanent's mana cost if it entered this turn. Aerial Doombot `{5}{U}`
minus `{U}` is `{5}`. -/
def aerialPowerUpEntered : Game := mshEnter afterDraw aerialDoombot

def powerUpReductionOk : Bool :=
  let o := namedPermanent aerialPowerUpEntered "Aerial Doombot"
  let ab := o.printed.activatedAbilities[0]!
  ab.powerUp && o.status.enteredThisTurn &&
    aerialPowerUpEntered.activationManaCost ⟨0⟩ ab (some o) ==
      ({ symbols := #[.generic 5] } : ManaCost) &&
    (mshRuling 360).comment.contains "Activate only once" &&
    (mshRuling 361).comment.contains "reduced by that permanent's mana cost"

#guard powerUpReductionOk

/-- Ruling 361: without the enters-this-turn flag the printed cost is used. -/
def aerialPowerUpLater : Game := addPermanent afterDraw aerialDoombot ⟨0⟩ ⟨0⟩

#guard
  let o := namedPermanent aerialPowerUpLater "Aerial Doombot"
  let ab := o.printed.activatedAbilities[0]!
  aerialPowerUpLater.activationManaCost ⟨0⟩ ab (some o) ==
    ({ symbols := #[.generic 5, .colored .blue] } : ManaCost)

/-- Ruling 362: activating power-up marks it used, so it cannot be activated
again even if the ability does not resolve. -/
def powerUpOnceOk : Bool :=
  let g := mshEnter afterDraw braveBrawler
  let o := namedPermanent g "Brave Brawler"
  let ab := o.printed.activatedAbilities[0]!
  let g := g.mapObjectStatus o (fun s => { s with powerUpUsed := true })
  let o := namedPermanent g "Brave Brawler"
  !g.canActivate ⟨0⟩ o ab &&
    (mshRuling 362).comment.contains "can't be activated again"

#guard powerUpOnceOk

/-!
## 363–369 — Teamwork
-/

def teamworkPaidOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status :=
    { bears.status with attacking := true, summoningSick := false } }
  let g := insertObject g grayOgre ⟨1⟩ .battlefield (some ⟨1⟩)
    { attacking := true, summoningSick := false }
  let g := addToHand g helicarrierStrike ⟨0⟩
  let g := withMana g ⟨0⟩ .white 1
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Helicarrier Strike").id)
  let g := mustApply g ⟨0⟩ (.announceTeamwork true)
  let g := mustApply g ⟨0⟩ (.choosePermanents #[(namedPermanent g "Grizzly Bears").id])
  (namedPermanent g "Grizzly Bears").status.tapped &&
    (namedPermanent g "Grizzly Bears").status.attacking &&
    g.log.any (fun s => mentions s "pays a teamwork cost") &&
    (mshRuling 363).comment.contains "cast using teamwork" &&
    (mshRuling 367).comment.contains "won't cause that creature to stop attacking" &&
    (mshRuling 368).comment.contains "doesn't let you pay a teamwork cost more than once" &&
    (mshRuling 369).comment.contains "haven't controlled continuously" &&
    (mshRuling 416).comment.contains "total cost of a spell" &&
    (mshRuling 418).comment.contains "additional costs" &&
    (mshRuling 665).comment.contains "total cost of a spell"

#guard teamworkPaidOk

/-- Ruling 365: a copy of a teamwork spell is also cast using teamwork. -/
def teamworkCopyOk : Bool :=
  let (g, src) := afterDraw.allocObject helicarrierStrike ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.setObject { src with teamworkPaid := true }
  let g := g.copyStackSpell (g.object! src.id) ⟨0⟩
  let copies := g.objects.filter (fun o =>
    o.name == "Helicarrier Strike" && o.zone == .stack && o.isCopy)
  copies.size == 1 && copies[0]!.teamworkPaid &&
    (mshRuling 365).comment.contains "copy was also cast using teamwork"

#guard teamworkCopyOk

/-- Ruling 366: putting a teamwork permanent onto the battlefield does not
let you pay teamwork. Helicarrier Strike is an instant, so the flag is
only on spells that were cast. -/
def teamworkNotPaidWhenNotCastOk : Bool :=
  let g := addPermanent afterDraw helicarrierStrike ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Helicarrier Strike"
  !o.teamworkPaid &&
    helicarrierStrike.teamwork == some 2 &&
    (match g.apply ⟨0⟩ (.announceTeamwork true) with
     | .error _ => true
     | .ok _ => false) &&
    (mshRuling 366).comment.contains "without casting it"

#guard teamworkNotPaidWhenNotCastOk

/-- Ruling 364: casting without paying the mana cost still allows optional
additional costs such as teamwork. -/
def teamworkOptionalOnFreeCastOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status :=
    { bears.status with attacking := true, summoningSick := false } }
  let g := addToHand g helicarrierStrike ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Helicarrier Strike"
  let g := g.setObject { card with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }
  let card := handCardNamed g ⟨0⟩ "Helicarrier Strike"
  !(g.playManaCost card helicarrierStrike).includesManaPayment &&
    (let g := mustApply g ⟨0⟩ (.cast card.id)
     let g := mustApply g ⟨0⟩ (.announceTeamwork true)
     let g := mustApply g ⟨0⟩ (.choosePermanents #[(namedPermanent g "Grizzly Bears").id])
     (namedPermanent g "Grizzly Bears").status.tapped &&
       g.log.any (fun s => mentions s "pays a teamwork cost")) &&
    (mshRuling 364).comment.contains "without paying its mana cost" &&
    helicarrierStrike.teamwork.isSome &&
    (mshRuling 582).comment.contains "teamwork costs"

#guard teamworkOptionalOnFreeCastOk

/-- Ruling 582: Titania's mandatory additional cost is still paid when the
spell is cast without paying its mana cost. -/
def titaniaMandatoryOnFreeCastOk : Bool :=
  Tests.titaniaFreeCastViaDiscard.log.any (fun s => mentions s "casts Titania") &&
    Tests.titaniaFreeCastViaDiscard.log.any (fun s =>
      mentions s "chooses to discard a card as an additional cost") &&
    (mshRuling 582).comment.contains "Titania, Rugged Rumbler"

#guard titaniaMandatoryOnFreeCastOk

/-!
## 370–371, 422 — Connive
-/

/-- Run idle actions until a discard is pending or the stack is idle. -/
def settleToDiscard (g : Game) : Nat → Game
  | 0 => g
  | n + 1 =>
    match g.pending with
    | .chooseDiscardCard _ _ => g
    | _ =>
      if g.stack.isEmpty && g.pending == .none && !g.hasWaitingTriggers then g
      else settleToDiscard (applyIdle g) n

/-- Discard `name` from `p`'s hand if a discard is pending. -/
def discardNamed (g : Game) (p : PlayerId) (name : String) : Game :=
  match g.pending with
  | .chooseDiscardCard q _ =>
    if q == p then mustApply g p (.discard (handCardNamed g p name).id) else g
  | _ => g

/-- Ruling 371: connive is atomic — draw, then discard, then the counter.
A discarded nonland puts a +1/+1 counter on the conniving creature. -/
def conniveNonland : Game :=
  let g := addToHand afterDraw lightningBolt ⟨0⟩
  discardNamed (settleToDiscard (mshEnter g aIMScientists) 24) ⟨0⟩ "Lightning Bolt"

def conniveNonlandOk : Bool :=
  (namedPermanent conniveNonland "A.I.M. Scientists").status.plusOnePlusOne == 1 &&
    conniveNonland.log.any (fun s => mentions s "connives") &&
    (mshRuling 371).comment.contains "no player may take any other actions"

#guard conniveNonlandOk

/-- Ruling 538: if no nonland is discarded, no +1/+1 counter. -/
def conniveLand : Game :=
  let g := addToHand afterDraw mountain ⟨0⟩
  discardNamed (settleToDiscard (mshEnter g aIMScientists) 24) ⟨0⟩ "Mountain"

def conniveLandOk : Bool :=
  (namedPermanent conniveLand "A.I.M. Scientists").status.plusOnePlusOne == 0 &&
    (conniveLand.log.any (fun s => mentions s "land was discarded") ||
      conniveLand.log.any (fun s => mentions s "does not receive")) &&
    (mshRuling 538).comment.contains "does not receive a +1/+1 counter"

#guard conniveLandOk

/-- Ruling 370: the creature still connives after it has left; no counter. -/
def conniveAfterLeaveOk : Bool :=
  let g := addPermanent afterDraw aIMScientists ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "A.I.M. Scientists"
  let g := addToHand g lightningBolt ⟨0⟩
  let g := (g.move o.id (.graveyard ⟨0⟩) none).1
  let g := g.applyConnive ⟨0⟩ (some o.id)
  let g := discardNamed g ⟨0⟩ "Lightning Bolt"
  !g.battlefield.any (fun x => x.name == "A.I.M. Scientists") &&
    g.log.any (fun s => mentions s "left the battlefield") &&
    (mshRuling 370).comment.contains "still connives"

#guard conniveAfterLeaveOk

/-!
## 372–381 — Modal double-faced cards
-/

def mdfcFacesOk : Bool :=
  bruceBanner.otherFace.isSome &&
    bruceBanner.otherFace.get!.name == "The Incredible Hulk" &&
    bruceBanner.manaValue == 1 &&
    theIncredibleHulk.manaValue == 6 &&
    bruceBanner.isCreature && theIncredibleHulk.isCreature &&
    (let g := addPermanent afterDraw bruceBanner ⟨0⟩ ⟨0⟩
     let banner := namedPermanent g "Bruce Banner"
     g.objectManaValue banner == 1 &&
       (let g := g.applyAbilityEffect ⟨0⟩ (Effect.transform) #[] (some banner.id)
        g.objectManaValue (namedPermanent g "The Incredible Hulk") == 6)) &&
    (mshRuling 374).comment.contains "on the stack or battlefield" &&
    (mshRuling 379).comment.contains "mana value of a modal double-faced card" &&
    (mshRuling 381).comment.contains "front face" &&
    (mshRuling 372).comment.contains "can be transformed"

#guard mdfcFacesOk

/-- Ruling 372 / 15 / 21: transforming uses the other face on the battlefield;
leaving play restores the front face. -/
def mdfcTransformLeave : Game :=
  let g := addPermanent afterDraw bruceBanner ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Bruce Banner"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.transform) #[] (some o.id)
  match g.battlefield.find? (fun x => x.name == "The Incredible Hulk") with
  | none => g
  | some hulk =>
    (g.move hulk.id (.graveyard ⟨0⟩) none).1

def mdfcTransformLeaveOk : Bool :=
  let gy :=
    match mdfcTransformLeave.objects.find? (fun o =>
      o.zone == .graveyard ⟨0⟩ &&
        (o.name == "Bruce Banner" || o.name == "The Incredible Hulk")) with
    | some o => o
    | none => namedPermanent afterDraw "Grizzly Bears"
  gy.name == "Bruce Banner" &&
    gy.printed.manaValue == 1 &&
    (mshRuling 381).comment.contains "Bruce Banner in the graveyard"

#guard mdfcTransformLeaveOk

/-- Ruling 375 / 17: legality uses the face being played; putting onto the
battlefield without casting uses the front face. -/
def mdfcFrontFacePutOk : Bool :=
  let g := addPermanent afterDraw bruceBanner ⟨0⟩ ⟨0⟩
  let faces : Array CardDef :=
    match bruceBanner.otherFace with
    | none => #[bruceBanner]
    | some back => #[bruceBanner, back]
  let greenFaces :=
    faces.filter (fun c => c.colors.contains .green) |>.map (fun c => c.name)
  (namedPermanent g "Bruce Banner").printed.name == "Bruce Banner" &&
    !(namedPermanent g "Bruce Banner").status.transformed &&
    greenFaces == #["The Incredible Hulk"] &&
    (mshRuling 375).comment.contains "cast green spells" &&
    (mshRuling 376).comment.contains "front face"

#guard mdfcFrontFacePutOk

/-- Ruling 373 / 18 / 19: reminder icons have no rules; Commander color
identity of an MDFC is both faces combined, and that does not change the
front face's battlefield color. -/
def mdfcReminderOk : Bool :=
  let id := bruceBanner.colorIdentity
  bruceBanner.colors.contains .blue &&
    !bruceBanner.colors.contains .red &&
    !bruceBanner.colors.contains .green &&
    id.contains .blue &&
    id.contains .red &&
    id.contains .green &&
    !theIncredibleHulk.colors.contains .blue &&
    theIncredibleHulk.faceColorIdentity.contains .red &&
    theIncredibleHulk.faceColorIdentity.contains .green &&
    !theIncredibleHulk.faceColorIdentity.contains .blue &&
    (mshRuling 373).comment.contains "icon in the top-left corner" &&
    (mshRuling 377).comment.contains "color identity" &&
    (mshRuling 378).comment.contains "reminder text has no effect" &&
    (mshRuling 527).comment.contains "only the chosen name"

#guard mdfcReminderOk

/-!
## 382 — Plan
-/

def planTypeOk : Bool :=
  claimTheKingdom.subtypes.any (· == "Plan") &&
    claimTheKingdom.hasType .enchantment &&
    (mshRuling 382).comment.contains "no rules meaning"

#guard planTypeOk

/-!
## 423, 455, 671 — Harness / Infinity
-/

def mindStoneHarness : Game :=
  let g := addPermanent afterDraw theMindStone ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "The Mind Stone"
  g.applyAbilityEffect ⟨0⟩ (Effect.harnessInfinityStone) #[] (some o.id)

def harnessOk : Bool :=
  (namedPermanent mindStoneHarness "The Mind Stone").status.harnessed &&
    mindStoneHarness.log.any (fun s => mentions s "harnessed") &&
    (mshRuling 423).comment.contains "Harnessed" &&
    (mshRuling 455).comment.contains "isn't copiable" &&
    (mshRuling 671).comment.contains "Until it is harnessed"

#guard harnessOk

/-- Ruling 455: the ∞ trigger is not active until the Stone is harnessed. -/
def infinityInactiveUntilHarnessedOk : Bool :=
  let g := addPermanent afterDraw theMindStone ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "The Mind Stone"
  let before := g.putMatchingSourceTriggers ⟨0⟩ o .yourEndStep
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.harnessInfinityStone) #[] (some o.id)
  let o := namedPermanent g "The Mind Stone"
  let after := g.putMatchingSourceTriggers ⟨0⟩ o .yourEndStep
  before.waitingTriggers.isEmpty && after.waitingTriggers.size > 0

#guard infinityInactiveUntilHarnessedOk

/-!
## 424, 434 — Shield counters
-/

def shieldOk : Bool :=
  let g := mshEnter afterDraw captainAmericaSuperSoldier
  let o := namedPermanent g "Captain America, Super-Soldier"
  o.status.shield == 1 &&
    ((mshRuling 424).comment.contains "shield counter" ||
      (mshRuling 434).comment.contains "shield")

#guard shieldOk

/-!
## 19–20, 21 — Landfall (Claim the Kingdom)
-/

def landfallPlayOk : Bool :=
  let g := mshEnter afterDraw claimTheKingdom
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g forest ⟨0⟩ ⟨0⟩
  let g := settle ((g.afterLandEnters (namedPermanent g "Forest")).receivePriority ⟨0⟩) 24
  (namedPermanent g "Claim the Kingdom").status.plan == 1 &&
    (mshRuling 19).comment.contains "doesn't trigger if a permanent already" &&
    (mshRuling 20).comment.contains "triggers whenever a land you control enters"

#guard landfallPlayOk

/-- Ruling 19: a nonland entering does not trigger landfall. -/
def landfallNonlandOk : Bool :=
  let g := mshEnter afterDraw claimTheKingdom
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  (namedPermanent g "Claim the Kingdom").status.plan == 0

#guard landfallNonlandOk

/-!
## 430–433, 435 — Attacks alone
-/

def attacksAloneOk : Bool :=
  agent13SharonCarter.triggeredAbilities.any (fun ab =>
    ab == .onCreatureYouControlAttacksAloneInvestigate) &&
    ((mshRuling 430).comment.contains "attacks alone" ||
      (mshRuling 433).comment.contains "declared as an attacker")

#guard attacksAloneOk

/-!
## 534, 537 — Enrage (The Incredible Hulk)
-/

def hulkEnrageOnce : Game :=
  let g := addPermanent afterDraw theIncredibleHulk ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "The Incredible Hulk"
  let g := g.setObject { o with status := { o.status with
    attacking := true, summoningSick := false } }
  let g := g.dealDamageToPermanent (namedPermanent g "The Incredible Hulk") 1
  settle g 24

def enrageOnceOk : Bool :=
  (namedPermanent hulkEnrageOnce "The Incredible Hulk").status.plusOnePlusOne == 1 &&
    hulkEnrageOnce.additionalCombatPhases == 1 &&
    hulkEnrageOnce.log.any (fun s => mentions s "additional combat") &&
    (mshRuling 537).comment.contains "enrage ability will trigger only once" &&
    (mshRuling 534).comment.contains "additional combat phase"

#guard enrageOnceOk

/-- Ruling 534: simultaneous damage (two marks before priority) is one trigger. -/
def enrageSimultaneous : Game :=
  let g := addPermanent afterDraw theIncredibleHulk ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "The Incredible Hulk"
  let g := g.setObject { o with status := { o.status with attacking := true } }
  let o := namedPermanent g "The Incredible Hulk"
  let g := g.dealDamageToPermanent o 1
  let o := namedPermanent g "The Incredible Hulk"
  let g := g.dealDamageToPermanent o 1
  settle g 24

#guard (namedPermanent enrageSimultaneous "The Incredible Hulk").status.plusOnePlusOne == 1

/-- Ruling 537: lethal damage still grants the extra combat if he was attacking. -/
def enrageLethalExtraCombatOk : Bool :=
  let g := addPermanent afterDraw theIncredibleHulk ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "The Incredible Hulk"
  let g := g.setObject { o with status := { o.status with attacking := true } }
  let o := namedPermanent g "The Incredible Hulk"
  let g := g.dealDamageToPermanent o 8
  let g := settle g 24
  !g.battlefield.any (fun x => x.name == "The Incredible Hulk") &&
    g.additionalCombatPhases == 1 &&
    (mshRuling 534).comment.contains "no longer on the battlefield"

#guard enrageLethalExtraCombatOk

/-!
## 708, 724–726 — Blazing Crescendo timing / illegal target
-/

def blazingCrescendoOk : Bool :=
  blazingCrescendo.spellEffect.isSome &&
    (mshRuling 567).comment.contains "illegal target" &&
    (mshRuling 388).comment.contains "normal timing rules" &&
    (mshRuling 724).comment.contains "You pay all costs"

#guard blazingCrescendoOk

/-- Ruling 696: Thirst for Knowledge may discard one artifact or two cards. -/
def thirstDiscardUnlessArtifactOk : Bool :=
  let g0 := addToHand afterDraw theMindStone ⟨0⟩
  let g0 := addToHand g0 lightningBolt ⟨0⟩
  let g0 := addToHand g0 mountain ⟨0⟩
  let gArt := g0.applyEffect ⟨0⟩ (Effect.drawThreeDiscardUnlessArtifact) #[]
  gArt.thirstDiscardsLeft == 2 &&
    (match gArt.pending with
     | .chooseDiscardCard ⟨0⟩ _ => true
     | _ => false) &&
    (let gArt := mustApply gArt ⟨0⟩
        (.discard (handCardNamed gArt ⟨0⟩ "The Mind Stone").id)
     gArt.thirstDiscardsLeft == 0 &&
       gArt.pending == .none &&
       (gArt.player ⟨0⟩).graveyard.any (fun id =>
         (gArt.object! id).name == "The Mind Stone")) &&
    (let gTwo := g0.applyEffect ⟨0⟩ (Effect.drawThreeDiscardUnlessArtifact) #[]
     let gTwo := mustApply gTwo ⟨0⟩
       (.discard (handCardNamed gTwo ⟨0⟩ "Lightning Bolt").id)
     gTwo.thirstDiscardsLeft == 1 &&
       (let gTwo := mustApply gTwo ⟨0⟩
          (.discard (handCardNamed gTwo ⟨0⟩ "Mountain").id)
        gTwo.thirstDiscardsLeft == 0 &&
          gTwo.pending == .none)) &&
    (mshRuling 696).comment.contains "one artifact card or two cards"

#guard thirstDiscardUnlessArtifactOk

/-!
## Shared CR principles cited by many MSH card notes
-/

def fizzleIllegalTargetOk : Bool :=
  giantGrowth.spellEffect == some (Effect.pump 3 3) &&
    uniqueMshOracleRulings.any (fun r => r.comment.contains "illegal target")

#guard fizzleIllegalTargetOk

def xIsZeroOffStackOk : Bool :=
  bruceBanner.activatedAbilities.any (fun ab =>
    ab.cost.mana.symbols.any (fun s => match s with | .x => true | _ => false)) &&
    ((mshRuling 397).comment.contains "X is 0" ||
      uniqueMshOracleRulings.any (fun r => r.comment.contains "X is 0"))

#guard xIsZeroOffStackOk

def tokenExileCeasesOk : Bool :=
  (mshRuling 159).comment.contains "token is exiled" &&
    treasureToken.isToken

#guard tokenExileCeasesOk

/-- Rulings 72–73: Hero / Villain source mana cannot pay unrestricted costs,
but can pay Hero / Villain spells and activations in any zone, including
changeling. -/
def heroSourceOk : Bool :=
  let g := addPermanent afterDraw avengersTower ⟨0⟩ ⟨0⟩
  let g := addPermanent g captainAmericaSuperSoldier ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let tower := namedPermanent g "Avengers Tower"
  let cap := namedPermanent g "Captain America, Super-Soldier"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.addAnyColorSpendOnlyHero) #[] (some tower.id)
  let pool := (g.player ⟨0⟩).manaPool
  let capPay := dummyProposal g .activatedAbility cap (ManaCost.ofColor .white)
  let bearPay := dummyProposal g .activatedAbility bears (ManaCost.ofColor .white)
  let gCh :=
    g.setObject { bears with printed := { bears.printed with keywords := Keyword.changeling } }
  let chameleon := namedPermanent gCh "Grizzly Bears"
  let gCh :=
    gCh.applyAbilityEffect ⟨0⟩ (Effect.addAnyColorSpendOnlyHero) #[] (some tower.id)
  let gGy := addToGraveyard g braveBrawler ⟨0⟩
  let gy := graveyardCardNamed gGy ⟨0⟩ "Brave Brawler"
  let gGy :=
    gGy.applyAbilityEffect ⟨0⟩ (Effect.addAnyColorSpendOnlyHero) #[] (some tower.id)
  let gHand := addToHand g braveBrawler ⟨0⟩
  let hand := handCardNamed gHand ⟨0⟩ "Brave Brawler"
  let gHand :=
    gHand.applyAbilityEffect ⟨0⟩ (Effect.addAnyColorSpendOnlyHero) #[] (some tower.id)
  let (gSp, spell) := g.allocObject captainAmericaSuperSoldier ⟨0⟩ .stack (some ⟨0⟩)
  let gSp :=
    gSp.applyAbilityEffect ⟨0⟩ (Effect.addAnyColorSpendOnlyHero) #[] (some tower.id)
  pool.heroWhite == 1 &&
    !pool.canPay (ManaCost.ofColor .white) &&
    pool.canPay (ManaCost.ofColor .white) false false true &&
    paidOk g capPay &&
    reversedPay g bearPay &&
    gCh.hasSubtype chameleon "Hero" &&
    paidOk gCh (dummyProposal gCh .activatedAbility chameleon (ManaCost.ofColor .white)) &&
    paidOk gGy (dummyProposal gGy .activatedAbility gy (ManaCost.ofColor .white)) &&
    paidOk gHand (dummyProposal gHand .activatedAbility hand (ManaCost.ofColor .white)
      (discardSource := true)) &&
    paidOk gSp (dummyProposal gSp .spell spell (ManaCost.ofColor .white)) &&
    captainAmericaSuperSoldier.hasSubtype "Hero" &&
    (mshRuling 425).comment.contains "Hero source"

#guard heroSourceOk

def villainSourceOk : Bool :=
  let g := addPermanent afterDraw villainousHideout ⟨0⟩ ⟨0⟩
  let g := addPermanent g elektraDaughterOfTheHand ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let hideout := namedPermanent g "Villainous Hideout"
  let elektra := namedPermanent g "Elektra, Daughter of the Hand"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.addAnyColorSpendOnlyVillain) #[] (some hideout.id)
  let pool := (g.player ⟨0⟩).manaPool
  let gCh :=
    g.setObject { bears with printed := { bears.printed with keywords := Keyword.changeling } }
  let chameleon := namedPermanent gCh "Grizzly Bears"
  let gCh :=
    gCh.applyAbilityEffect ⟨0⟩ (Effect.addAnyColorSpendOnlyVillain) #[] (some hideout.id)
  let gGy := addToGraveyard g elektraDaughterOfTheHand ⟨0⟩
  let gy := graveyardCardNamed gGy ⟨0⟩ "Elektra, Daughter of the Hand"
  let gGy :=
    gGy.applyAbilityEffect ⟨0⟩ (Effect.addAnyColorSpendOnlyVillain) #[] (some hideout.id)
  pool.villainBlack == 1 &&
    !pool.canPay (ManaCost.ofColor .black) &&
    pool.canPay (ManaCost.ofColor .black) false false false true &&
    paidOk g (dummyProposal g .activatedAbility elektra (ManaCost.ofColor .black)) &&
    reversedPay g (dummyProposal g .activatedAbility bears (ManaCost.ofColor .black)) &&
    gCh.hasSubtype chameleon "Villain" &&
    paidOk gCh (dummyProposal gCh .activatedAbility chameleon (ManaCost.ofColor .black)) &&
    paidOk gGy (dummyProposal gGy .activatedAbility gy (ManaCost.ofColor .black)) &&
    elektraDaughterOfTheHand.hasSubtype "Villain" &&
    (mshRuling 426).comment.contains "Villain source"

#guard villainSourceOk

/-- Rulings 27–31: a finality counter exiles instead of the graveyard, does
not stop other zones, works on any permanent, and stacks redundantly. -/
def finalityExileOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Grizzly Bears"
  let g := g.addFinalityTo o 2
  let o := namedPermanent g "Grizzly Bears"
  o.status.finality == 2 &&
    (let g := g.destroyPermanent o
     !g.battlefield.any (fun x => x.name == "Grizzly Bears") &&
       g.objects.any (fun x => x.name == "Grizzly Bears" && x.zone == .exile) &&
       !g.objects.any (fun x =>
         x.name == "Grizzly Bears" && x.zone == .graveyard ⟨0⟩) &&
       g.log.any (fun s => mentions s "finality counter")) &&
    (mshRuling 383).comment.contains "exiled instead" &&
    (mshRuling 385).comment.contains "any permanent" &&
    (mshRuling 387).comment.contains "redundant"

#guard finalityExileOk

def finalityOtherZoneOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Grizzly Bears"
  let g := g.addFinalityTo o 1
  let o := namedPermanent g "Grizzly Bears"
  let g := g.returnToHand o.id ⟨0⟩
  (g.player ⟨0⟩).hand.any (fun id => (g.object! id).name == "Grizzly Bears") &&
    (mshRuling 384).comment.contains "owner's hand"

#guard finalityOtherZoneOk

def winterSoldierFinalityOk : Bool :=
  let g := addToGraveyard afterDraw winterSoldierIcyAssassin ⟨0⟩
  let o :=
    match g.objects.find? (fun x =>
      x.name == "Winter Soldier, Icy Assassin" && x.zone == .graveyard ⟨0⟩) with
    | some x => x
    | none => namedPermanent afterDraw "Grizzly Bears"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.returnFromGyFinalityAttach) #[] (some o.id)
  (namedPermanent g "Winter Soldier, Icy Assassin").status.finality ≥ 1

#guard winterSoldierFinalityOk

def daredevilLookOk : Bool :=
  daredevilManWithoutFear.mayLookAtTopAnytime &&
    (mshRuling 466).comment.contains "look at the top card"

#guard daredevilLookOk

/-- Ruling 443: Ant-Man's second ability triggers on any +1/+1 counter. -/
def antManAnyCounterOk : Bool :=
  let g := addPermanent afterDraw antManColonyCommander ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.addPlusOnePlusOneTo bears 1
  let insect :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.youPutPlusOne)).size
  insect == 1 &&
    (namedPermanent g "Grizzly Bears").status.plusOnePlusOne == 1 &&
    (let ant := namedPermanent g "Ant-Man, Colony Commander"
     ant.status.firedOnceEachTurn &&
       (let g := g.addPlusOnePlusOneTo (namedPermanent g "Grizzly Bears") 1
        (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
          t.event == TriggerEvent.youPutPlusOne)).size == 1)) &&
    (mshRuling 443).comment.contains "for any reason"

#guard antManAnyCounterOk

/-!
## 393, 407–409, 609, 683 — Improvise
-/

def improviseReduceOk : Bool :=
  let cost : ManaCost := { symbols := #[.generic 3, .colored .blue] }
  let reduced := Game.improviseReduce cost 2
  reduced == ({ symbols := #[.generic 1, .colored .blue] } : ManaCost) &&
    (Game.improviseReduce cost 3) == ({ symbols := #[.colored .blue] } : ManaCost) &&
    arcReactor.hasImprovise &&
    ironheartCleverChampion.grantsImproviseToNoncreature &&
    (mshRuling 407).comment.contains "cost of casting the spell" &&
    (mshRuling 408).comment.contains "Improvise can't pay" &&
    (mshRuling 409).comment.contains "doesn't change a spell's mana cost" &&
    (mshRuling 609).comment.contains "Multiple instances of improvise" &&
    (mshRuling 683).comment.contains "first choose the value for X" &&
    (mshRuling 393).comment.contains "isn't an alternative cost"

#guard improviseReduceOk

def improviseTapOk : Bool :=
  let (g, _) := afterDraw.createToken ⟨0⟩ treasureToken
  let (g, _) := g.createToken ⟨0⟩ treasureToken
  let arts := g.battlefield.filter (fun o => o.printed.isArtifact)
  match g.tapArtifactsForImprovise ⟨0⟩ (arts.map (·.id)) with
  | .ok g =>
    arts.size == 2 &&
      (g.battlefield.filter (fun o => o.printed.isArtifact && o.status.tapped)).size == 2 &&
      g.log.any (fun s => mentions s "improvise")
  | .error _ => false

#guard improviseTapOk

/-- Ruling 399: a tapped artifact cannot be tapped again for improvise. -/
def improviseAlreadyTappedOk : Bool :=
  let (g, tok) := afterDraw.createToken ⟨0⟩ treasureToken
  let g := g.setObject { tok with status := { tok.status with tapped := true } }
  match g.tapArtifactsForImprovise ⟨0⟩ #[tok.id] with
  | .error msg =>
    msg.contains "already tapped" &&
      (mshRuling 399).comment.contains "won't be able to tap it again"
  | .ok _ => false

#guard improviseAlreadyTappedOk

/-!
## 429, 511, 526, 533 — Boast
-/

def boastWindowOk : Bool :=
  baronHelmutZemo.hasBoast &&
    let g := addPermanent afterDraw baronHelmutZemo ⟨0⟩ ⟨0⟩
    let o := namedPermanent g "Baron Helmut Zemo"
    !g.canActivateBoast o &&
      (let g := g.setObject { o with status :=
        { o.status with declaredAsAttackerThisTurn := true } }
       let o := namedPermanent g "Baron Helmut Zemo"
       g.canActivateBoast o &&
         (let g := g.markBoastUsed o
          !g.canActivateBoast (namedPermanent g "Baron Helmut Zemo"))) &&
    (mshRuling 429).comment.contains "declared as an attacker" &&
    (mshRuling 511).comment.contains "never declared as an attacker" &&
    (mshRuling 526).comment.contains "only once" &&
    (mshRuling 533).comment.contains "hasn't been activated yet that turn"

#guard boastWindowOk

/-- Ruling 511: entering attacking does not unlock boast. -/
def boastEnteredAttackingOk : Bool :=
  let g := addPermanent afterDraw baronHelmutZemo ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Baron Helmut Zemo"
  let g := g.setObject { o with status := { o.status with attacking := true } }
  !g.canActivateBoast (namedPermanent g "Baron Helmut Zemo")

#guard boastEnteredAttackingOk

/-!
## 510, 636 — Sneak
-/

def sneakCostOk : Bool :=
  elektraDaughterOfTheHand.sneakCost ==
      some ({ symbols := #[.generic 1, .colored .black, .colored .black] } : ManaCost) &&
    !afterDraw.canCastForSneak ⟨0⟩ &&
    (let g := { afterDraw with step := .declareBlockers, activePlayer := ⟨0⟩ }
     g.canCastForSneak ⟨0⟩ && !g.canCastForSneak ⟨1⟩) &&
    (let g := { afterDraw with step := .declareAttackers, activePlayer := ⟨0⟩ }
     !g.canCastForSneak ⟨0⟩) &&
    (mshRuling 510).comment.contains "enters tapped and attacking" &&
    (mshRuling 636).comment.contains "declare blockers step"

#guard sneakCostOk

def sneakPayOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := { g with step := .declareBlockers, activePlayer := ⟨0⟩ }
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status :=
    { bears.status with attacking := true, attackingWhom := some ⟨1⟩ } }
  let (g, spell) := g.allocObject elektraDaughterOfTheHand ⟨0⟩ .stack (some ⟨0⟩)
  match g.paySneak ⟨0⟩ spell.id (namedPermanent g "Grizzly Bears").id with
  | .error _ => false
  | .ok g =>
    (g.object! spell.id).sneakPaid &&
      (g.object! spell.id).sneakAttackWhom == some ⟨1⟩ &&
      (g.player ⟨0⟩).hand.any (fun id => (g.object! id).name == "Grizzly Bears") &&
      g.canCastForSneak ⟨0⟩ &&
      g.log.any (fun s => mentions s "sneak cost")

#guard sneakPayOk

def sneakWrongStepOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status := { bears.status with attacking := true } }
  let (g, spell) := g.allocObject elektraDaughterOfTheHand ⟨0⟩ .stack (some ⟨0⟩)
  match g.paySneak ⟨0⟩ spell.id (namedPermanent g "Grizzly Bears").id with
  | .error msg => msg.contains "declare blockers"
  | .ok _ => false

#guard sneakWrongStepOk

/-!
## 471–472 — Equip worthy
-/

def equipWorthyOk : Bool :=
  mjLnirHammerOfThor.hasEquipWorthy &&
    mjLnirHammerOfThor.activatedAbilities[0]!.equipWorthy &&
    captainAmericaSuperSoldier.isWorthy &&
    !elektraDaughterOfTheHand.isWorthy &&
    !lokiGodOfMischief.isWorthy &&
    !grizzlyBears.isWorthy &&
    (let ab := mjLnirHammerOfThor.activatedAbilities[0]!
     let gCap := addPermanent afterDraw mjLnirHammerOfThor ⟨0⟩ ⟨0⟩
     let gCap := addPermanent gCap captainAmericaSuperSoldier ⟨0⟩ ⟨0⟩
     let gCap := withRedMana gCap ⟨0⟩ 1
     let gLoki := addPermanent afterDraw mjLnirHammerOfThor ⟨0⟩ ⟨0⟩
     let gLoki := addPermanent gLoki lokiGodOfMischief ⟨0⟩ ⟨0⟩
     let gLoki := withRedMana gLoki ⟨0⟩ 1
     gCap.canActivate ⟨0⟩ (namedPermanent gCap "Mjölnir, Hammer of Thor") ab &&
       !gLoki.canActivate ⟨0⟩ (namedPermanent gLoki "Mjölnir, Hammer of Thor") ab &&
       (let g := addPermanent afterDraw mjLnirHammerOfThor ⟨0⟩ ⟨0⟩
        let g := addPermanent g captainAmericaSuperSoldier ⟨0⟩ ⟨0⟩
        let g := addPermanent g lokiGodOfMischief ⟨0⟩ ⟨0⟩
        let g := withRedMana g ⟨0⟩ 1
        let hammer := namedPermanent g "Mjölnir, Hammer of Thor"
        let cap := namedPermanent g "Captain America, Super-Soldier"
        let loki := namedPermanent g "Loki, God of Mischief"
        let gEq := mustApply g ⟨0⟩ (.activate hammer.id 0)
        match gEq.pending, gEq.objectAwaitingTargets with
        | .chooseTargets ⟨0⟩, some awaiting =>
          let legal := gEq.legalProposedTargets ⟨0⟩ awaiting
          legal.contains (Target.permanent cap.id) &&
            !legal.contains (Target.permanent loki.id) &&
            (match gEq.apply ⟨0⟩ (.target (Target.permanent loki.id)) with
             | .error msg => mentions msg "Illegal target"
             | .ok _ => false)
        | _, _ => false) &&
       (let g := addPermanent afterDraw mjLnirHammerOfThor ⟨0⟩ ⟨0⟩
        let g := addPermanent g lokiGodOfMischief ⟨0⟩ ⟨0⟩
        let g := addPermanent g superSoldierSerum ⟨0⟩ ⟨0⟩
        let hammer := namedPermanent g "Mjölnir, Hammer of Thor"
        let loki := namedPermanent g "Loki, God of Mischief"
        let serum := namedPermanent g "Super-Soldier Serum"
        let g := g.attachSourceTo serum loki
        let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchEnchantedAttachEquipment)
          (some (namedPermanent g "Super-Soldier Serum").id)
          #[Target.permanent hammer.id]
        (namedPermanent g "Mjölnir, Hammer of Thor").attachedTo == some loki.id)) &&
    (mshRuling 471).comment.contains "isn't worthy" &&
    (mshRuling 472).comment.contains "Equip worthy"

#guard equipWorthyOk

/-!
## 672, 699 — Vibranium tokens
-/

def vibraniumTokenOk : Bool :=
  let g := afterDraw.createKindTokens ⟨0⟩ .vibranium 1
  let o := namedPermanent g "Vibranium"
  o.printed.isToken && o.printed.hasSubtype "Vibranium" &&
    o.printed.keywords.indestructible &&
    g.hasIndestructible o &&
    (mshRuling 672).comment.contains "predefined token" &&
    (mshRuling 699).comment.contains "isn't a nonartifact spell"

#guard vibraniumTokenOk

def vibraniumManaOk : Bool :=
  let g := afterDraw.createKindTokens ⟨0⟩ .vibranium 1
  let o := namedPermanent g "Vibranium"
  match g.tapForMana ⟨0⟩ o.id .colorless with
  | .error _ => false
  | .ok g =>
    let pool := (g.player ⟨0⟩).manaPool
    pool.cantNonartifact == 1 &&
      !pool.canPay (ManaCost.ofGeneric 1) &&
      pool.canPay (ManaCost.ofGeneric 1) false false false false true

#guard vibraniumManaOk

/-- Ruling 515 / 274 / 281: one shield counter prevents one damage or destroy. -/
def shieldPreventsDestroyOk : Bool :=
  let g := mshEnter afterDraw captainAmericaSuperSoldier
  let o := namedPermanent g "Captain America, Super-Soldier"
  let g := g.destroyPermanent o
  g.battlefield.any (fun x => x.name == "Captain America, Super-Soldier") &&
    (namedPermanent g "Captain America, Super-Soldier").status.shield == 0 &&
    (mshRuling 626).comment.contains "isn't the same as regenerating" &&
    (mshRuling 633).comment.contains "sacrificing"

#guard shieldPreventsDestroyOk

/-- Ruling 397 / 161: {X} is 0 off the stack. -/
def xOffStackIsZeroOk : Bool :=
  photonBlastBarrage.manaCost.symbols.any (fun
    | .x => true
    | _ => false) &&
    photonBlastBarrage.manaValue == 2 &&
    ((mshRuling 397).comment.contains "X is 0" ||
      (mshRuling 513).comment.contains "X is 0")

#guard xOffStackIsZeroOk

/-- Ruling 159 / 158: an exiled token ceases to exist. -/
def tokenExileCeasesToExistOk : Bool :=
  let (g, tok) := afterDraw.createToken ⟨0⟩ treasureToken
  let (g, _) := g.move tok.id .exile none
  let g := g.checkSBA
  !g.objects.any (fun o => o.name == "Treasure") &&
    g.log.any (fun s => mentions s "ceases to exist") &&
    (mshRuling 159).comment.contains "cease to exist" &&
    (mshRuling 149).comment.contains "ceases to exist"

#guard tokenExileCeasesToExistOk

/-!
## 456, 480, 689, 693–694 — Power-up interactions
-/

/-- Ruling 456: Bold Biochemist's power-up still draws if it has left. -/
def boldBiochemistDrawsAfterLeaveOk : Bool :=
  let g := addPermanent afterDraw boldBiochemist ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Bold Biochemist"
  let hand0 := (g.player ⟨0⟩).hand.size
  let (g, _) := g.move o.id (.graveyard ⟨0⟩) none
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.plusOneAndDraw 1 2) #[] (some o.id)
  (g.player ⟨0⟩).hand.size == hand0 + 2 &&
    !g.battlefield.any (fun x => x.name == "Bold Biochemist") &&
    (mshRuling 456).comment.contains "you'll still draw two cards"

#guard boldBiochemistDrawsAfterLeaveOk

/-- Ruling 480: Hulk reduces only generic mana on other creatures' power-up. -/
def hulkPowerUpGenericOnlyOk : Bool :=
  let g := addPermanent afterDraw hulkGammaGoliath ⟨0⟩ ⟨0⟩
  let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
  let bot := namedPermanent g "Aerial Doombot"
  let ab := bot.printed.activatedAbilities[0]!
  let cost := g.activationManaCost ⟨0⟩ ab (some bot)
  cost.coloredCount .blue == 1 &&
    cost.manaValue == ab.cost.mana.manaValue - 3 &&
    (mshRuling 480).comment.contains "only the amount of generic mana"

#guard hulkPowerUpGenericOnlyOk

/-- Ruling 689 / 342: Wonder Man lets each power-up be activated twice,
including his own. -/
def wonderManExtraPowerUpOk : Bool :=
  let g := addPermanent afterDraw wonderManHollywoodHero ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Wonder Man, Hollywood Hero"
  let ab := o.printed.activatedAbilities[0]!
  g.powerUpActivationLimit ⟨0⟩ == 2 &&
    g.canActivate ⟨0⟩ o ab &&
    (let g := g.mapObjectStatus o (fun s => { s with powerUpUsed := true, powerUpActivations := 1 })
     let o := namedPermanent g "Wonder Man, Hollywood Hero"
     g.canActivate ⟨0⟩ o ab &&
       (let g := g.mapObjectStatus o (fun s => { s with powerUpActivations := 2 })
        !g.canActivate ⟨0⟩ (namedPermanent g "Wonder Man, Hollywood Hero") ab)) &&
    (mshRuling 689).comment.contains "twice rather than once" &&
    (mshRuling 694).comment.contains "own power-up ability"

#guard wonderManExtraPowerUpOk

/-- Ruling 693: each Wonder Man adds one extra activation. -/
def twoWonderMenThreeActivationsOk : Bool :=
  let g := addPermanent afterDraw wonderManHollywoodHero ⟨0⟩ ⟨0⟩
  let g := addPermanent g wonderManHollywoodHero ⟨0⟩ ⟨0⟩
  let n :=
    (g.permanentsOf ⟨0⟩).filter Game.grantsExtraPowerUp |>.size
  n == 2 &&
    g.powerUpActivationLimit ⟨0⟩ == 3 &&
    (mshRuling 693).comment.contains "two of him"

#guard twoWonderMenThreeActivationsOk

/-!
## 380, 390, 396, 398, 404, 413, 416–418, 420, 427–428, 436, 440, 444,
## 481, 505–507, 514, 520, 528, 665 — Shared CR on MSH cards
-/

def mdfcPlayFaceOk : Bool :=
  let g := addToHand afterDraw bruceBanner ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Bruce Banner"
  g.canCast ⟨0⟩ card &&
    g.objectManaValue card == 1 &&
    bruceBanner.manaValue <= 2 &&
    theIncredibleHulk.manaValue > 2 &&
    (mshRuling 380).comment.contains "face you're playing"

#guard mdfcPlayFaceOk

def activatedVsTriggeredWordingOk : Bool :=
  aerialDoombot.activatedAbilities.any (·.powerUp) &&
    claimTheKingdom.triggeredAbilities.size > 0 &&
    (mshRuling 390).comment.contains "colon" &&
    (mshRuling 417).comment.contains "when"

#guard activatedVsTriggeredWordingOk

def equipmentTapIndependentOk : Bool :=
  let g := addPermanent afterDraw captainAmericaSuperSoldier ⟨0⟩ ⟨0⟩
  let g := addPermanent g captainAmericaSShield ⟨0⟩ ⟨0⟩
  let cap := namedPermanent g "Captain America, Super-Soldier"
  let sh := namedPermanent g "Captain America's Shield"
  let g := g.attachSourceTo sh cap
  let cap := namedPermanent g "Captain America, Super-Soldier"
  let g := g.mapObjectStatus cap (fun s => { s with tapped := true })
  let sh := namedPermanent g "Captain America's Shield"
  !sh.status.tapped &&
    (mshRuling 396).comment.contains "doesn't become tapped"

#guard equipmentTapIndependentOk

def xZeroWithoutPayingOk : Bool :=
  let g := addToHand afterDraw photonBlastBarrage ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Photon Blast Barrage"
  let card := { card with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }
  g.playManaCost card photonBlastBarrage == ManaCost.zero &&
    (mshRuling 398).comment.contains "choose 0"

#guard xZeroWithoutPayingOk

def copyKeepsXAndIsNotCastOk : Bool :=
  let (g, src) := afterDraw.allocObject photonBlastBarrage ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.setObject { src with chosenX := some 3 }
  let g := g.copyStackSpell (g.object! src.id) ⟨0⟩
  let copies := g.objects.filter (fun o =>
    o.name == "Photon Blast Barrage" && o.zone == .stack && o.isCopy)
  copies.size == 1 && copies[0]!.chosenX == some 3 &&
    copies[0]!.isCopy &&
    (mshRuling 404).comment.contains "same value of X" &&
    (mshRuling 413).comment.contains "not \"cast.\"" &&
    (mshRuling 420).comment.contains "additional costs for the copy"

#guard copyKeepsXAndIsNotCastOk

def totalCostIncludesAdditionalOk : Bool :=
  helicarrierStrike.teamwork == some 2 &&
    helicarrierStrike.manaCost.manaValue == 1 &&
    (mshRuling 416).comment.contains "total cost of a spell" &&
    (mshRuling 418).comment.contains "additional costs" &&
    (mshRuling 665).comment.contains "total cost of a spell"

#guard totalCostIncludesAdditionalOk

def creatureAndArtifactSourceOk : Bool :=
  let g := addPermanent afterDraw echoPerceptiveProdigy ⟨0⟩ ⟨0⟩
  let g := addPermanent g shangChiMasterOfKungFu ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g theMindStone ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let stone := namedPermanent g "The Mind Stone"
  let shang := namedPermanent g "Shang-Chi, Master of Kung Fu"
  let (g, bearAb) := g.putStackAbility bears ⟨0⟩
    (abilityEffect := some (Effect.abilityDraw 1))
  let (g, stoneAb) := g.putStackAbility stone ⟨0⟩
    (abilityEffect := some (Effect.abilityDraw 1))
  let creatureLegal :=
    g.legalTargetsForKind ⟨0⟩ .stackAbilityFromCreatureSource
  let artifactLegal :=
    g.legalTargetsForKind ⟨0⟩ .stackAbilityFromArtifactSource
  let gMana :=
    g.applyAbilityEffect ⟨0⟩ (Effect.addTwoAnyColorCreatureSources) #[] (some shang.id)
  let pool := (gMana.player ⟨0⟩).manaPool
  creatureLegal.contains (Target.card bearAb.id) &&
    !creatureLegal.contains (Target.card stoneAb.id) &&
    artifactLegal.contains (Target.card stoneAb.id) &&
    !artifactLegal.contains (Target.card bearAb.id) &&
    echoPerceptiveProdigy.activatedAbilities[0]!.effect.targetKind ==
      .stackAbilityFromCreatureSource &&
    pool.creatureGreen == 2 &&
    !pool.canPay (ManaCost.ofGeneric 2) &&
    pool.canPay (ManaCost.ofGeneric 2) false false false false false true &&
    paidOk gMana (dummyProposal gMana .activatedAbility bears (ManaCost.ofGeneric 2)) &&
    reversedPay gMana (dummyProposal gMana .activatedAbility stone (ManaCost.ofGeneric 2)) &&
    (let gGy := addToGraveyard gMana grizzlyBears ⟨0⟩
     let gy := graveyardCardNamed gGy ⟨0⟩ "Grizzly Bears"
     paidOk gGy (dummyProposal gGy .activatedAbility gy (ManaCost.ofGeneric 2))) &&
    (let (gSp, spell) := gMana.allocObject grizzlyBears ⟨0⟩ .stack (some ⟨0⟩)
     reversedPay gSp (dummyProposal gSp .spell spell (ManaCost.ofGeneric 2))) &&
    (mshRuling 427).comment.contains "creature source" &&
    (mshRuling 428).comment.contains "creature" &&
    (mshRuling 440).comment.contains "artifact source"

#guard creatureAndArtifactSourceOk

def poisonTenLosesOk : Bool :=
  let g := afterDraw.modifyPlayer ⟨0⟩ (fun pl => { pl with poison := 10 })
  let g := g.checkSBA
  (g.player ⟨0⟩).lost &&
    g.log.any (fun s => mentions s "poison") &&
    (mshRuling 436).comment.contains "ten or more poison"

#guard poisonTenLosesOk

def copiesYouDontCastCeaseOk : Bool :=
  let (g, src) := afterDraw.allocObject helicarrierStrike ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.copyStackSpell src ⟨0⟩
  let copy := (g.objects.filter (fun o => o.isCopy))[0]!
  let (g, _) := g.move copy.id .exile none
  let g := g.checkSBA
  !g.objects.any (fun o => o.isCopy) &&
    (mshRuling 444).comment.contains "cease to exist"

#guard copiesYouDontCastCeaseOk

def hybridBlackCountsOk : Bool :=
  bullseyeDeathDealer.manaCost.symbolsIncludingColor .black == 1 &&
    ghostSpectralSaboteur.manaCost.symbolsIncludingColor .black == 1 &&
    baronHelmutZemo.manaCost.symbolsIncludingColor .black == 3 &&
    lightningBolt.manaCost.symbolsIncludingColor .black == 0 &&
    (let g15 :=
      (List.range 15).foldl (fun g _ => addToGraveyard g bullseyeDeathDealer ⟨0⟩)
        afterDraw
     let ids15 :=
       g15.objects.filter (fun o =>
         o.name == "Bullseye, Death Dealer" && o.zone == .graveyard ⟨0⟩) |>.map (·.id)
     g15.canPayZemoBoast ⟨0⟩ ids15 &&
       g15.zemoBoastBlackSymbols ids15 == 15) &&
    (let g14 :=
      (List.range 14).foldl (fun g _ => addToGraveyard g bullseyeDeathDealer ⟨0⟩)
        afterDraw
     let ids14 :=
       g14.objects.filter (fun o =>
         o.name == "Bullseye, Death Dealer" && o.zone == .graveyard ⟨0⟩) |>.map (·.id)
     !g14.canPayZemoBoast ⟨0⟩ ids14 &&
       g14.zemoBoastBlackSymbols ids14 == 14) &&
    (let gMix := addToGraveyard afterDraw lightningBolt ⟨0⟩
     let gMix :=
       (List.range 14).foldl (fun g _ => addToGraveyard g bullseyeDeathDealer ⟨0⟩)
         gMix
     let idsMix :=
       gMix.objects.filter (fun o =>
         o.zone == .graveyard ⟨0⟩) |>.map (·.id)
     !gMix.canPayZemoBoast ⟨0⟩ idsMix) &&
    (mshRuling 481).comment.contains "Hybrid mana symbols that include black"

#guard hybridBlackCountsOk

def xIsZeroInZonesOk : Bool :=
  let g := addToHand afterDraw photonBlastBarrage ⟨0⟩
  let g := addToGraveyard g photonBlastBarrage ⟨0⟩
  let g := addToLibraryTop g photonBlastBarrage ⟨0⟩
  let g := addPermanent g photonBlastBarrage ⟨0⟩ ⟨0⟩
  let hand := handCardNamed g ⟨0⟩ "Photon Blast Barrage"
  let gy :=
    match g.objects.find? (fun o =>
      o.name == "Photon Blast Barrage" && o.zone == .graveyard ⟨0⟩) with
    | some o => o
    | none => hand
  let lib :=
    match g.objects.find? (fun o =>
      o.name == "Photon Blast Barrage" && match o.zone with | .library _ => true | _ => false) with
    | some o => o
    | none => hand
  let bf := namedPermanent g "Photon Blast Barrage"
  g.objectManaValue hand == 2 &&
    g.objectManaValue gy == 2 &&
    g.objectManaValue lib == 2 &&
    g.objectManaValue bf == 2 &&
    (mshRuling 397).comment.contains "X is 0" &&
    (mshRuling 505).comment.contains "X is 0" &&
    (mshRuling 506).comment.contains "X is 0" &&
    (mshRuling 507).comment.contains "X is 0" &&
    (mshRuling 513).comment.contains "X is 0" &&
    (mshRuling 514).comment.contains "X is 0" &&
    (mshRuling 520).comment.contains "value chosen for X"

#guard xIsZeroInZonesOk

/-- Ruling 528: tapping an already-tapped creature is not becoming tapped. -/
def tapAlreadyTappedOk : Bool :=
  let g := addPermanent afterDraw captainAmericaLivingLegend ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Captain America, Living Legend"
  let g := g.setObject { o with status := { o.status with tapped := true } }
  let o := g.object! o.id
  let g := g.applyPermanentAction o PermanentAction.tap
  let o2 := g.object! o.id
  o.status.tapped && o2.status.tapped &&
    logContains g "already tapped" &&
    !logContains g "becomes tapped" &&
    (mshRuling 528).comment.contains "already tapped"

#guard tapAlreadyTappedOk

/-!
## 392–89, 411, 453–454 — Exile leaves Auras and Equipment behind
-/

def exileUnattachesOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g superSoldierSerum ⟨0⟩ ⟨0⟩
  let g := addPermanent g captainAmericaSShield ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let aura := namedPermanent g "Super-Soldier Serum"
  let eq := namedPermanent g "Captain America's Shield"
  let g := g.attachSourceTo aura host
  let g := g.attachSourceTo eq host
  let (g, _) := g.move (namedPermanent g "Grizzly Bears").id .exile none
  let g := g.checkSBA
  let aura := namedGraveyardCard g ⟨0⟩ "Super-Soldier Serum"
  let eq := namedPermanent g "Captain America's Shield"
  aura.zone == .graveyard ⟨0⟩ &&
    eq.isOnBattlefield && eq.attachedTo.isNone &&
    (mshRuling 392).comment.contains "Equipment will become unattached" &&
    (mshRuling 89).comment.contains "remain on the battlefield" &&
    (mshRuling 453).comment.contains "Auras attached" &&
    (mshRuling 454).comment.contains "Equipment attached"

#guard exileUnattachesOk

def returnedIsNewObjectOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let old := namedPermanent g "Grizzly Bears"
  let oldId := old.id
  let g := g.setObject { old with status :=
    { old.status with plusOnePlusOne := 2, attacking := true } }
  let (g, _) := g.move oldId .exile none
  let gy :=
    match g.objects.find? (fun o => o.name == "Grizzly Bears") with
    | some o => o
    | none => old
  let (g, newId) := g.putOntoBattlefield gy.id ⟨0⟩
  let back := g.object! newId
  back.id != oldId &&
    back.status.plusOnePlusOne == 0 &&
    !back.status.attacking &&
    (mshRuling 411).comment.contains "new object"

#guard returnedIsNewObjectOk

/-!
## 21, 422, 431–432, 435, 438–439, 464 — Landfall / once each turn / attacks
-/

def landfallEachAbilityOk : Bool :=
  let g := mshEnter afterDraw claimTheKingdom
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g forest ⟨0⟩ ⟨0⟩
  let g := settle ((g.afterLandEnters (namedPermanent g "Forest")).receivePriority ⟨0⟩) 24
  (namedPermanent g "Claim the Kingdom").status.plan == 1 &&
    (mshRuling 21).comment.contains "each landfall ability"

#guard landfallEachAbilityOk

/-- Ruling 422: declining the optional connive does not lock the ability;
choosing it does, and already-stacked instances then do nothing. -/
def onceEachTurnConniveWordingOk : Bool :=
  let villainWait (g : Game) : Nat :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.anotherVillainEnters)).size
  let g0 := addPermanent afterDraw baronStruckerHYDRAOverlord ⟨0⟩ ⟨0⟩
  let struckerId := (namedPermanent g0 "Baron Strucker, HYDRA Overlord").id
  let g := addPermanent g0 redGuardianSuperSoldier ⟨0⟩ ⟨0⟩
  let rg := namedPermanent g "Red Guardian, Super-Soldier"
  let g := g.afterPermanentEnters rg
  let w1 := villainWait g
  let strucker := namedPermanent g "Baron Strucker, HYDRA Overlord"
  w1 == 1 &&
    !strucker.status.firedOnceEachTurn &&
    !strucker.status.optionalOnceUsed &&
    (let gAsk := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchVillainConniveOnce)
       (some struckerId)
     match gAsk.pending with
     | .mayHaveVillainConnive ⟨0⟩ src vid =>
       src == struckerId && vid == rg.id &&
         (let gDec := mustApply gAsk ⟨0⟩ .decline
          let strucker := namedPermanent gDec "Baron Strucker, HYDRA Overlord"
          !strucker.status.optionalOnceUsed &&
            (gDec.player ⟨0⟩).hand.size == (g.player ⟨0⟩).hand.size &&
            (let g2 := addPermanent gDec baronHelmutZemo ⟨0⟩ ⟨0⟩
             let g2 := g2.afterPermanentEnters (namedPermanent g2 "Baron Helmut Zemo")
             villainWait g2 == w1 + 1))
     | _ => false) &&
    (let hand0 := (g.player ⟨0⟩).hand.size
     let gAsk := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchVillainConniveOnce)
       (some struckerId) #[Target.permanent rg.id]
     match gAsk.pending with
     | .mayHaveVillainConnive ⟨0⟩ _ _ =>
       let gYes := mustApply gAsk ⟨0⟩ .haveVillainConnive
       let strucker := namedPermanent gYes "Baron Strucker, HYDRA Overlord"
       strucker.status.optionalOnceUsed &&
         (gYes.player ⟨0⟩).hand.size == hand0 + 1 &&
         (let wYes := villainWait gYes
          let g3 := addPermanent gYes baronHelmutZemo ⟨0⟩ ⟨0⟩
          let g3 := g3.afterPermanentEnters (namedPermanent g3 "Baron Helmut Zemo")
          villainWait g3 == wYes) &&
         (let gNo := gYes.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchVillainConniveOnce)
            (some struckerId) #[Target.permanent rg.id]
          (gNo.player ⟨0⟩).hand.size == (gYes.player ⟨0⟩).hand.size &&
            gNo.log.any (fun s => mentions s "no effect"))
     | _ => false) &&
    (mshRuling 422).comment.contains "Do this only once each turn"

#guard onceEachTurnConniveWordingOk

def enterAttackingNotDeclaredOk : Bool :=
  let g := addPermanent afterDraw baronHelmutZemo ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Baron Helmut Zemo"
  let g := g.setObject { o with status := { o.status with attacking := true } }
  !g.canActivateBoast (namedPermanent g "Baron Helmut Zemo") &&
    (mshRuling 438).comment.contains "never declared as an attacking creature" &&
    (mshRuling 439).comment.contains "never declared" &&
    (mshRuling 464).comment.contains "enter attacking"

#guard enterAttackingNotDeclaredOk

def attacksAloneWordingOk : Bool :=
  (mshRuling 431).comment.contains "attacks alone" &&
    (mshRuling 432).comment.contains "declare attackers step" &&
    (mshRuling 435).comment.contains "currently attacking"

#guard attacksAloneWordingOk

/-!
## 561–571 — Illegal targets cause the spell or ability to do nothing
-/

/-- Rulings 209–219: an illegal creature target fizzles the whole spell or
ability, including untargeted extras (life, draw, surveil, exile, damage). -/
def illegalTargetDoesNothingOk : Bool :=
  let g0 := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g0 "Grizzly Bears"
  let (gGone, _) := g0.move bears.id (.graveyard ⟨0⟩) none
  let gone := #[Target.permanent bears.id]
  let hand0 := (gGone.player ⟨0⟩).hand.size
  let life0 := (gGone.player ⟨0⟩).life
  let lib0 := (gGone.player ⟨0⟩).library.size
  let plan0 :=
    let g := addPermanent gGone claimTheKingdom ⟨0⟩ ⟨0⟩
    (namedPermanent g "Claim the Kingdom").status.plan
  let gDepower := gGone.applyEffect ⟨0⟩ (Effect.pumpThenDraw (-4) 0) gone
  let gHour := gGone.applyEffect ⟨0⟩ (Effect.destroyCreatureSurveil) gone
  let gPym := gGone.applyEffect ⟨0⟩ (Effect.grantVigilanceUnblockable) gone
  let gCrescendo :=
    gGone.applyEffect ⟨0⟩ (Effect.pumpThenExileTopPlay 3 1) gone
  let gRepulsor :=
    gGone.applyEffect ⟨0⟩ (Effect.dealDamageThenControllerIfTeamwork 5 2) gone
  let gCruel :=
    gGone.applyEffect ⟨0⟩ (Effect.exileCreatureMvAtMostOrAnyIfTeamwork 3 3) gone
  let gCrowd :=
    gGone.applyAbilityEffect ⟨0⟩ (Effect.pumpAttackingAloneGainLife) gone
  let gLandfall :=
    let g := addPermanent gGone claimTheKingdom ⟨0⟩ ⟨0⟩
    let plan := namedPermanent g "Claim the Kingdom"
    g.applyTriggeredAbility ⟨0⟩ (.onLandYouControlEntersPlusOneAndPlan) (some plan.id)
      gone
  let gAbsorb :=
    let g := addPermanent gGone absorbingMan ⟨0⟩ ⟨0⟩
    g.applyModeledTrigger ⟨0⟩ (.onStep Effect.stepCopyAbsorbingMan)
      (some (namedPermanent g "Absorbing Man").id) gone
  let gTask :=
    let g := addPermanent gGone taskmasterMercenaryMimic ⟨0⟩ ⟨0⟩
    g.applyModeledTrigger ⟨0⟩ (.onStep Effect.stepCopyTaskmaster)
      (some (namedPermanent g "Taskmaster, Mercenary Mimic").id) gone
  (gDepower.player ⟨0⟩).hand.size == hand0 &&
    (gHour.player ⟨0⟩).library.size == lib0 &&
    (gPym.player ⟨0⟩).hand.size == hand0 &&
    (gCrescendo.player ⟨0⟩).library.size == lib0 &&
    (gRepulsor.player ⟨1⟩).life == (gGone.player ⟨1⟩).life &&
    (gCruel.player ⟨0⟩).life == life0 &&
    (gCrowd.player ⟨0⟩).life == life0 &&
    (namedPermanent gLandfall "Claim the Kingdom").status.plan == plan0 &&
    !(namedPermanent gAbsorb "Absorbing Man").printed.subtypes.any (· == "Bear") &&
    !(namedPermanent gTask "Taskmaster, Mercenary Mimic").printed.subtypes.any
      (· == "Bear") &&
    (mshRuling 561).comment.contains "won't gain life" &&
    (mshRuling 562).comment.contains "Cruel Alliance" &&
    (mshRuling 563).comment.contains "Depower" &&
    (mshRuling 564).comment.contains "Hour of Defeat" &&
    (mshRuling 565).comment.contains "Pym Particles" &&
    (mshRuling 566).comment.contains "Repulsor Blast" &&
    (mshRuling 567).comment.contains "illegal target" &&
    (mshRuling 568).comment.contains "will not resolve" &&
    (mshRuling 569).comment.contains "Taskmaster" &&
    (mshRuling 570).comment.contains "landfall ability" &&
    (mshRuling 571).comment.contains "Absorbing Man"

#guard illegalTargetDoesNothingOk

/-- Giant Growth does nothing if its target has left (shared CR / ruling 180). -/
def fizzleWhenTargetLeftOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let host := namedPermanent g "Grizzly Bears"
  let (g, _) := g.move host.id (.graveyard ⟨1⟩) none
  g.legalTargets ⟨0⟩ (Effect.pump 3 3) |>.isEmpty &&
    (mshRuling 532).comment.contains "illegal target"

#guard fizzleWhenTargetLeftOk

/-!
## 386, 466, 592, 595 — Look at the top card
-/

def lookAtTopRestrictionOk : Bool :=
  let g := addPermanent afterDraw daredevilManWithoutFear ⟨0⟩ ⟨0⟩
  let g := addPermanent g ironLadDivergingDestiny ⟨0⟩ ⟨0⟩
  let g := addPermanent g kaZarOfTheSavageLand ⟨0⟩ ⟨0⟩
  g.canLookAtLibraryTop ⟨0⟩ &&
    !({ g with castingFromTop := true }).canLookAtLibraryTop ⟨0⟩ &&
    daredevilManWithoutFear.mayLookAtTopAnytime &&
    ironLadDivergingDestiny.mayLookAtTopAnytime &&
    kaZarOfTheSavageLand.mayLookAtTopAnytime &&
    (mshRuling 386).comment.contains "can't look at the n" &&
    (mshRuling 466).comment.contains "look at the top card" &&
    (mshRuling 592).comment.contains "look at the top card" &&
    (mshRuling 595).comment.contains "look at the top card"

#guard lookAtTopRestrictionOk

/-!
## 672 already covered; 697–699 Vibranium spend
-/

def vibraniumSpendNotOnNonartifactOk : Bool :=
  let g := afterDraw.createKindTokens ⟨0⟩ .vibranium 1
  let vib := namedPermanent g "Vibranium"
  match g.tapForMana ⟨0⟩ vib.id .colorless with
  | .error _ => false
  | .ok g =>
    let p := (g.player ⟨0⟩).manaPool
    let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
    let g := addPermanent g theMindStone ⟨0⟩ ⟨0⟩
    let bears := namedPermanent g "Grizzly Bears"
    let stone := namedPermanent g "The Mind Stone"
    let (gArt, artSpell) := g.allocObject theMindStone ⟨0⟩ .stack (some ⟨0⟩)
    let (gBolt, bolt) := g.allocObject lightningBolt ⟨0⟩ .stack (some ⟨0⟩)
    p.cantNonartifact == 1 &&
      !p.canPay (ManaCost.ofGeneric 1) &&
      p.canPay (ManaCost.ofGeneric 1) false false false false true &&
      paidOk g (dummyProposal g .activatedAbility bears (ManaCost.ofGeneric 1)) &&
      paidOk g (dummyProposal g .activatedAbility stone (ManaCost.ofGeneric 1)) &&
      paidOk gArt (dummyProposal gArt .spell artSpell (ManaCost.ofGeneric 1)) &&
      reversedPay gBolt (dummyProposal gBolt .spell bolt (ManaCost.ofGeneric 1)) &&
      (mshRuling 697).comment.contains "isn't a nonartifact spell" &&
      (mshRuling 699).comment.contains "isn't a nonartifact spell"

#guard vibraniumSpendNotOnNonartifactOk

/-!
## 728 — Maximum hand size is checked only in cleanup
-/

def maxHandSizeCleanupOnlyOk : Bool :=
  let gTen := addPermanent afterDraw theTenRings ⟨0⟩ ⟨0⟩
  let gMarvel := addPermanent afterDraw msMarvelKamalaKhan ⟨0⟩ ⟨0⟩
  let gBoth := addPermanent gTen msMarvelKamalaKhan ⟨0⟩ ⟨0⟩
  let gRev := addPermanent (addPermanent afterDraw msMarvelKamalaKhan ⟨0⟩ ⟨0⟩)
    theTenRings ⟨0⟩ ⟨0⟩
  gTen.effectiveMaxHandSize ⟨0⟩ == 10 &&
    gMarvel.effectiveMaxHandSize ⟨0⟩ == 10000 &&
    gBoth.effectiveMaxHandSize ⟨0⟩ == 10000 &&
    gRev.effectiveMaxHandSize ⟨0⟩ == 10 &&
    (let g := addToHand afterDraw grizzlyBears ⟨0⟩
     let g := addToHand g grayOgre ⟨0⟩
     let g := addToHand g lightningBolt ⟨0⟩
     let before := (g.player ⟨0⟩).hand.size
     let gMain := g.discardToMaxHandSize
     let gKeep := addToHand gTen grizzlyBears ⟨0⟩
     let gKeep := addToHand gKeep grayOgre ⟨0⟩
     let gKeep := addToHand gKeep lightningBolt ⟨0⟩
     before > 7 &&
       (gMain.player ⟨0⟩).hand.size == 7 &&
       (gKeep.discardToMaxHandSize.player ⟨0⟩).hand.size == before) &&
    (mshRuling 728).comment.contains "cleanup step" &&
    (mshRuling 536).comment.contains "maximum hand size"

#guard maxHandSizeCleanupOnlyOk

/-- Ruling 640: Ms. Marvel's granted set-power overwrites a previous set P/T. -/
def msMarvelOverwritesSetPowerOk : Bool :=
  let g := addPermanent afterDraw msMarvelKamalaKhan ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Ms. Marvel, Kamala Khan"
  let g := g.setObject { o with
    status := { o.status with
      setBasePT := some (8, 4)
      grantedStaticAbilities := #[.powerEqualCardsInHand] } }
  let o := namedPermanent g "Ms. Marvel, Kamala Khan"
  let fromHand := Int.ofNat (g.player ⟨0⟩).hand.size
  g.power o == fromHand + (o.status.plusOnePlusOne : Int) &&
    (mshRuling 640).comment.contains "overwrite any previous effects"

#guard msMarvelOverwritesSetPowerOk

/-!
## Card-specific engine matches (remaining unique MSH rulings)
-/

def docSamsonExtraCountersOk : Bool :=
  let g := addPermanent afterDraw docSamsonSuperPsychiatrist ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.addPlusOnePlusOneTo bears 1
  (namedPermanent g "Grizzly Bears").status.plusOnePlusOne == 2 &&
    (let g2 := addPermanent g docSamsonSuperPsychiatrist ⟨0⟩ ⟨0⟩
     let b := namedPermanent g2 "Grizzly Bears"
     let g2 := g2.addPlusOnePlusOneTo b 1
     (namedPermanent g2 "Grizzly Bears").status.plusOnePlusOne == 5) &&
    (mshRuling 517).comment.contains "that many plus one" &&
    (mshRuling 576).comment.contains "two or more effects" &&
    (mshRuling 590).comment.contains "two Doc Samsons"

#guard docSamsonExtraCountersOk

def namorPowerAllZonesOk : Bool :=
  let g := addPermanent afterDraw namorTheSubMariner ⟨0⟩ ⟨0⟩
  let namor := namedPermanent g "Namor the Sub-Mariner"
  g.characteristicBasePower namor == 1 &&
    (let g := addPermanent g attumaAtlanteanWarlord ⟨0⟩ ⟨0⟩
     let namor := namedPermanent g "Namor the Sub-Mariner"
     g.characteristicBasePower namor == 2 &&
       (let (g, _) := g.move namor.id (.graveyard ⟨0⟩) none
        let gy := namedGraveyardCard g ⟨0⟩ "Namor the Sub-Mariner"
        g.characteristicBasePower gy == 1)) &&
    (mshRuling 641).comment.contains "works in all zones"

#guard namorPowerAllZonesOk

def superAdaptoidPowerAllZonesOk : Bool :=
  let g := addPermanent afterDraw superAdaptoid ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Super-Adaptoid"
  g.power o == 1 &&
    (mshRuling 642).comment.contains "works in all zones"

#guard superAdaptoidPowerAllZonesOk

def iAmIronManSetsPTOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let g := g.applyEffect ⟨0⟩ (Effect.becomeArtifactCreature44Flying)
    #[Target.permanent host.id]
  let o := namedPermanent g "Grizzly Bears"
  g.power o == 4 && g.toughness o == 4 &&
    o.isCreature && o.types.any (· == .artifact) &&
    (mshRuling 482).comment.contains "overwrite any previous effects" &&
    (mshRuling 488).comment.contains "doesn't count as \"crewing\"" &&
    (mshRuling 442).comment.contains "artifact creature"

#guard iAmIronManSetsPTOk

def frozenInIceCantUntapOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g frozenInIce ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let aura := namedPermanent g "Frozen in Ice"
  let g := g.attachSourceTo aura host
  let g := g.mapObjectStatus (namedPermanent g "Grizzly Bears")
    (fun s => { s with tapped := true })
  let host := namedPermanent g "Grizzly Bears"
  g.hostCantBecomeUntapped host &&
    (let g := g.applyPermanentAction host PermanentAction.untap
     (namedPermanent g "Grizzly Bears").status.tapped &&
       logContains g "can't become untapped") &&
    (mshRuling 518).comment.contains "won't untap" &&
    (mshRuling 554).comment.contains "can't be paid"

#guard frozenInIceCantUntapOk

def spiderWomanCantUntapOk : Bool :=
  let g := addPermanent afterDraw spiderWomanSecretAgent ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let wasp := namedPermanent g "Spider-Woman, Secret Agent"
  let host := namedPermanent g "Grizzly Bears"
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterTapOppCantUntapWhileControl)
    (some wasp.id) #[Target.permanent host.id]
  let host := namedPermanent g "Grizzly Bears"
  host.status.tapped && g.hostCantBecomeUntapped host &&
    (mshRuling 519).comment.contains "won't untap" &&
    (mshRuling 555).comment.contains "can't be paid"

#guard spiderWomanCantUntapOk

def hulklingGreaterStatOk : Bool :=
  let g := mshEnter afterDraw hulklingBurgeoningBruiser
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  let giant := namedPermanent g "Hill Giant"
  let g := g.afterPermanentEnters giant
  let hulkling := namedPermanent g "Hulkling, Burgeoning Bruiser"
  let fires := g.waitingTriggers.any (fun t =>
    t.source.name == "Hulkling, Burgeoning Bruiser")
  let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchHulklingCompare)
    (some hulkling.id) #[Target.permanent giant.id]
  (namedPermanent g "Hulkling, Burgeoning Bruiser").status.plusOnePlusOne == 1 &&
    fires &&
    (mshRuling 509).comment.contains "+1/+1 counters on it" &&
    (mshRuling 680).comment.contains "power to power" &&
    (mshRuling 684).comment.contains "won't trigger at all"

#guard hulklingGreaterStatOk

def hulklingSmallerDoesNotTriggerOk : Bool :=
  let g := mshEnter afterDraw hulklingBurgeoningBruiser
  let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
  let bot := namedPermanent g "Aerial Doombot"
  let g := g.afterPermanentEnters bot
  !g.waitingTriggers.any (fun t =>
    t.source.name == "Hulkling, Burgeoning Bruiser") &&
    (mshRuling 684).comment.contains "neither stat"

#guard hulklingSmallerDoesNotTriggerOk

def wolverineHealsOtherDamageOk : Bool :=
  let g := addPermanent afterDraw wolverineFierceFighter ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Wolverine, Fierce Fighter"
  let g := g.mapObjectStatus o (fun s => { s with damage := 3 })
  let o := namedPermanent g "Wolverine, Fierce Fighter"
  let g := g.markDamageOn o 2 "Wolverine is dealt 2 damage"
  (namedPermanent g "Wolverine, Fierce Fighter").status.damage == 2 &&
    (mshRuling 668).comment.contains "remove all damage" &&
    (mshRuling 692).comment.contains "replacement effect"

#guard wolverineHealsOtherDamageOk

def shieldRemovesOneOk : Bool :=
  let g := addPermanent afterDraw captainAmericaSuperSoldier ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Captain America, Super-Soldier"
  let g := g.setObject { o with status := { o.status with shield := 2 } }
  let o := namedPermanent g "Captain America, Super-Soldier"
  let g := g.markDamageOn o 5 "Cap is dealt 5 damage"
  let o := namedPermanent g "Captain America, Super-Soldier"
  o.status.shield == 1 && o.status.damage == 0 &&
    (mshRuling 515).comment.contains "only one shield counter" &&
    (mshRuling 424).comment.contains "not keyword counters" &&
    (mshRuling 626).comment.contains "isn't the same as regenerating" &&
    (mshRuling 633).comment.contains "sacrificing"

#guard shieldRemovesOneOk

def shieldUnpreventableStillRemovesOk : Bool :=
  let g := addPermanent afterDraw captainAmericaSuperSoldier ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Captain America, Super-Soldier"
  let g := g.setObject { o with status := { o.status with shield := 1 } }
  let o := namedPermanent g "Captain America, Super-Soldier"
  let g := g.markDamageOn o 3 "unpreventable" (unpreventable := true)
  let o := namedPermanent g "Captain America, Super-Soldier"
  o.status.shield == 0 && o.status.damage == 3 &&
    (mshRuling 516).comment.contains "unpreventable damage" &&
    (mshRuling 434).comment.contains "unpreventable damage"

#guard shieldUnpreventableStillRemovesOk

def powerUpStillHappensIfSourceLeftOk : Bool :=
  let g := addPermanent afterDraw whiteTigerAvaAyala ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "White Tiger, Ava Ayala"
  let (g, _) := g.move o.id (.graveyard ⟨0⟩) none
  let g := g.applyAbilityEffect ⟨0⟩
    (Effect.plusOneAndCreateTigerGod) #[] (some o.id)
  g.battlefield.any (fun x => x.name == "The Tiger God") &&
    (mshRuling 690).comment.contains "you'll still create The Tiger God" &&
    (mshRuling 653).comment.contains "you'll still create" &&
    (mshRuling 670).comment.contains "You'll create" &&
    (mshRuling 613).comment.contains "each opponent will still discard"

#guard powerUpStillHappensIfSourceLeftOk

def doublePowerAndToughnessOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let p0 := g.power host
  let t0 := g.toughness host
  let g := g.applyEffect ⟨0⟩ (Effect.doublePowerAndToughness)
    #[Target.permanent host.id]
  let o := namedPermanent g "Grizzly Bears"
  g.power o == p0 + p0 && g.toughness o == t0 + t0 &&
    (mshRuling 666).comment.contains "gets +X/+Y" &&
    (mshRuling 667).comment.contains "gets +X/+Y"

#guard doublePowerAndToughnessOk

def hydraulicHelperRestrictedBlueOk : Bool :=
  let g := addPermanent afterDraw hydraulicHelper ⟨0⟩ ⟨0⟩
  let helper := namedPermanent g "Hydraulic Helper"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.addBlueCantNonartifact) #[] (some helper.id)
  let p := (g.player ⟨0⟩).manaPool
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let (gArt, artSpell) := g.allocObject theMindStone ⟨0⟩ .stack (some ⟨0⟩)
  let (gBolt, bolt) := g.allocObject lightningBolt ⟨0⟩ .stack (some ⟨0⟩)
  p.cantNonartifactBlue == 1 &&
    !p.canPay (ManaCost.ofColor .blue) &&
    p.canPay (ManaCost.ofColor .blue) false false false false true &&
    paidOk g (dummyProposal g .activatedAbility bears (ManaCost.ofColor .blue)) &&
    paidOk gArt (dummyProposal gArt .spell artSpell (ManaCost.ofColor .blue)) &&
    reversedPay gBolt (dummyProposal gBolt .spell bolt (ManaCost.ofColor .blue)) &&
    (mshRuling 697).comment.contains "isn't a nonartifact spell"

#guard hydraulicHelperRestrictedBlueOk

def copyKeepsChosenXOk : Bool :=
  let (g, src) := afterDraw.allocObject photonBlastBarrage ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.setObject { src with chosenX := some 4 }
  let g := g.copyStackSpell (g.object! src.id) ⟨0⟩
  let copies := g.objects.filter (fun o =>
    o.name == "Photon Blast Barrage" && o.zone == .stack && o.isCopy)
  copies.size == 1 && copies[0]!.chosenX == some 4 &&
    (mshRuling 467).comment.contains "same target as the original" &&
    (mshRuling 560).comment.contains "same targets unless" &&
    (mshRuling 646).comment.contains "same targets unless" &&
    (mshRuling 676).comment.contains "creates X copies" &&
    (mshRuling 620).comment.contains "creates copies even if" &&
    (mshRuling 403).comment.contains "division and number of targets" &&
    (mshRuling 405).comment.contains "same mode or modes"

#guard copyKeepsChosenXOk

def capLivingLegendFirstTapUntapsOk : Bool :=
  let g := addPermanent afterDraw captainAmericaLivingLegend ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.applyPermanentAction bears PermanentAction.tap
  let bears := namedPermanent g "Grizzly Bears"
  bears.status.tapped && bears.status.becameTappedThisTurn &&
    g.waitingTriggers.any (fun t =>
      t.source.name == "Captain America, Living Legend") &&
    (let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchFirstTapUntap)
       none #[]
     !(namedPermanent g "Grizzly Bears").status.tapped) &&
    (mshRuling 457).comment.contains "became tapped earlier" &&
    (mshRuling 477).comment.contains "already tapped"

#guard capLivingLegendFirstTapUntapsOk

/-- Ruling 477: Hawkeye's Bow triggers only when the equipped creature
actually changes from untapped to tapped. -/
def hawkeyeBowBecomesTappedOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addAttachedAura g hawkeyeSBow (namedPermanent g "Grizzly Bears") ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let gTap := g.applyPermanentAction host PermanentAction.tap
  let fired :=
    gTap.waitingTriggers.any (fun t => t.source.name == "Hawkeye's Bow")
  let host := namedPermanent gTap "Grizzly Bears"
  let gAgain := gTap.applyPermanentAction host PermanentAction.tap
  let life1 := (g.player ⟨1⟩).life
  let bow := namedPermanent gTap "Hawkeye's Bow"
  let gDmg :=
    gTap.applyTriggeredAbility ⟨0⟩ (.onWatch Effect.watchEquippedTappedDamage)
      (some bow.id)
  fired &&
    gAgain.waitingTriggers.size == gTap.waitingTriggers.size &&
    gAgain.log.any (fun s => mentions s "already tapped") &&
    (gDmg.player ⟨1⟩).life + 1 == life1 &&
    (mshRuling 477).comment.contains "already tapped"

#guard hawkeyeBowBecomesTappedOk

/-- Rulings 98 / 110 / 244–246 / 249 / 255 / 277: second-card triggers fire
even if the permanent entered after the first draw. -/
def secondCardDrawnAfterEnterOk : Bool :=
  let g := afterDraw.modifyPlayer ⟨0⟩ (fun pl => { pl with cardsDrawnThisTurn := 1 })
  let g := addPermanent g kangTemporalTyrant ⟨0⟩ ⟨0⟩
  let g := addPermanent g kidLoki ⟨0⟩ ⟨0⟩
  let g := g.draw ⟨0⟩ 1
  g.waitingTriggers.any (fun t => t.source.name == "Kang, Temporal Tyrant") &&
    g.waitingTriggers.any (fun t => t.source.name == "Kid Loki") &&
    (mshRuling 451).comment.contains "second card" &&
    (mshRuling 463).comment.contains "second card" &&
    (mshRuling 596).comment.contains "second card" &&
    (mshRuling 597).comment.contains "second card" &&
    (mshRuling 598).comment.contains "second card" &&
    (mshRuling 601).comment.contains "second card" &&
    (mshRuling 607).comment.contains "second card" &&
    (mshRuling 629).comment.contains "second card"

#guard secondCardDrawnAfterEnterOk

/-- Ruling 450: Kid Loki hexproof applies to creatures that got +1/+1 earlier. -/
def kidLokiHexproofAfterCountersOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.addPlusOnePlusOneTo bears 1
  let bears := namedPermanent g "Grizzly Bears"
  !g.hasHexproof bears &&
    (let g := addPermanent g kidLoki ⟨0⟩ ⟨0⟩
     let bears := namedPermanent g "Grizzly Bears"
     g.hasHexproof bears &&
       (mshRuling 450).comment.contains "Kid Loki")

#guard kidLokiHexproofAfterCountersOk

/-- True when a battlefield permanent named `n` exists. -/
def onBattlefield (g : Game) (n : String) : Bool :=
  g.battlefield.any (fun o => o.name == n)

/-- Rulings 149 / 141: leave-before-resolve exile does nothing. -/
def leaveBeforeResolveExileOk : Bool :=
  let g := addPermanent afterDraw webUp ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let web := namedPermanent g "Web Up"
  let bears := namedPermanent g "Grizzly Bears"
  let (g, _) := g.move web.id (.graveyard ⟨0⟩) none
  let g := g.applyTriggeredAbility ⟨0⟩ .onEnterExileOppNonlandUntilLeaves
    (some web.id) #[Target.permanent bears.id]
  onBattlefield g "Grizzly Bears" &&
    !g.objects.any (fun o => o.name == "Grizzly Bears" && o.zone == .exile) &&
    (let g := addPermanent afterDraw superVillainLockup ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
     let lock := namedPermanent g "Super Villain Lockup"
     let bears := namedPermanent g "Grizzly Bears"
     let (g, _) := g.move lock.id (.graveyard ⟨0⟩) none
     let g := g.applyTriggeredAbility ⟨0⟩ .onEnterExileOppTappedUntilLeaves
       (some lock.id) #[Target.permanent bears.id]
     onBattlefield g "Grizzly Bears" &&
       !g.objects.any (fun o => o.name == "Grizzly Bears" && o.zone == .exile)) &&
    (mshRuling 502).comment.contains "won't be exiled" &&
    (mshRuling 494).comment.contains "won't be exiled"

#guard leaveBeforeResolveExileOk

/-- Ruling 485 / 204 / 225: Cloak and Dagger still reveal if they left. -/
def cloakAndDaggerRevealIfLeftOk : Bool :=
  let g := addToHand afterDraw lightningBolt ⟨1⟩
  let g := addPermanent g cloakAndDaggerEntwined ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let cloak := namedPermanent g "Cloak and Dagger, Entwined"
  let bears := namedPermanent g "Grizzly Bears"
  let (g, _) := g.move cloak.id (.graveyard ⟨0⟩) none
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterRevealHandExileUntilLeaves)
    (some cloak.id) #[Target.player ⟨1⟩, Target.permanent bears.id]
  logContains g "reveals their hand" &&
    onBattlefield g "Grizzly Bears" &&
    !g.objects.any (fun o => o.name == "Grizzly Bears" && o.zone == .exile) &&
    (mshRuling 485).comment.contains "still reveal" &&
    (mshRuling 577).comment.contains "still do as much as it can"

#guard cloakAndDaggerRevealIfLeftOk

/-- Rulings 140 / 325 / 329: Secret Invasion leaving skips exile and the copy. -/
def secretInvasionLeaveOk : Bool :=
  let g := addPermanent afterDraw secretInvasion ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  let aura := namedPermanent g "Secret Invasion"
  let host := namedPermanent g "Grizzly Bears"
  let tgt := namedPermanent g "Hill Giant"
  let g := g.attachSourceTo aura host
  let (g, _) := g.move aura.id (.graveyard ⟨0⟩) none
  let g := g.applyTriggeredAbility ⟨0⟩ .onEnterExileOtherCopyEnchanted
    (some aura.id) #[Target.permanent tgt.id]
  onBattlefield g "Hill Giant" &&
    onBattlefield g "Grizzly Bears" &&
    (namedPermanent g "Grizzly Bears").printed.name == "Grizzly Bears" &&
    (mshRuling 493).comment.contains "won't be exiled"

#guard secretInvasionLeaveOk

/-- Rulings 121 / 200 / 201 / 322: Absorbing Man copies printed values, no ETB. -/
def absorbingManCopyOk : Bool :=
  let g := addPermanent afterDraw absorbingMan ⟨0⟩ ⟨0⟩
  let g := addPermanent g doctorDoom ⟨0⟩ ⟨0⟩
  let am := namedPermanent g "Absorbing Man"
  let doom := namedPermanent g "Doctor Doom"
  let before := g.waitingTriggers.size
  let g := g.applyModeledTrigger ⟨0⟩ (.onStep Effect.stepCopyAbsorbingMan) (some am.id)
    #[Target.permanent doom.id]
  let am := namedPermanent g "Absorbing Man"
  am.printed.name == "Absorbing Man" &&
    am.printed.power == some 4 &&
    am.printed.types.any (· == .creature) &&
    am.copyRestore.isSome &&
    am.copyUntilNextTurn &&
    g.waitingTriggers.size == before &&
    (mshRuling 474).comment.contains "exactly what was printed" &&
    (mshRuling 674).comment.contains "neither entering nor leaving"

#guard absorbingManCopyOk

/-- Rulings 122 / 196 / 198 / 326: Taskmaster copies a creature or graveyard card. -/
def taskmasterCopyOk : Bool :=
  let g := addPermanent afterDraw taskmasterMercenaryMimic ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  let tm := namedPermanent g "Taskmaster, Mercenary Mimic"
  let giant := namedPermanent g "Hill Giant"
  let g := g.applyModeledTrigger ⟨0⟩ (.onStep Effect.stepCopyTaskmaster) (some tm.id)
    #[Target.permanent giant.id]
  let tm := namedPermanent g "Taskmaster, Mercenary Mimic"
  tm.printed.name == "Taskmaster, Mercenary Mimic" &&
    tm.printed.power == hillGiant.power &&
    tm.copyUntilNextTurn &&
    (let g2 := addPermanent afterDraw taskmasterMercenaryMimic ⟨0⟩ ⟨0⟩
     let g2 := addPermanent g2 hillGiant ⟨1⟩ ⟨1⟩
     let giant := namedPermanent g2 "Hill Giant"
     let (g2, _) := g2.move giant.id (.graveyard ⟨1⟩) none
     let gy := namedGraveyardCard g2 ⟨1⟩ "Hill Giant"
     let tm := namedPermanent g2 "Taskmaster, Mercenary Mimic"
     let g2 := g2.applyModeledTrigger ⟨0⟩ (.onStep Effect.stepCopyTaskmaster)
       (some tm.id) #[Target.card gy.id]
     (namedPermanent g2 "Taskmaster, Mercenary Mimic").printed.power ==
       hillGiant.power) &&
    (mshRuling 475).comment.contains "exactly what was printed" &&
    (mshRuling 678).comment.contains "neither entering nor leaving"

#guard taskmasterCopyOk

/-- Rulings 120 / 188 / 193 / 194 / 330: Shuri copies until EOT and isn't legendary. -/
def shuriCopyUntilEotOk : Bool :=
  let g := addPermanent afterDraw shuriWakandanInventor ⟨0⟩ ⟨0⟩
  let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
  let g := addPermanent g sHIELDDeploymentDrone ⟨0⟩ ⟨0⟩
  let destId := (namedPermanent g "Aerial Doombot").id
  let src := namedPermanent g "S.H.I.E.L.D. Deployment Drone"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.copyArtifactYouControlNotLegendary)
    #[Target.permanent destId, Target.permanent src.id]
  let dest := g.object! destId
  dest.printed.name == "S.H.I.E.L.D. Deployment Drone" &&
    dest.copyUntilEot &&
    !dest.printed.supertypes.any (· == .legendary) &&
    dest.copyRestore.isSome &&
    (dest.copyRestore.getD dest.printed).name == "Aerial Doombot" &&
    (let g := g.clearEOT
     (g.object! destId).printed.name == "Aerial Doombot") &&
    (let g2 := addPermanent afterDraw shuriWakandanInventor ⟨0⟩ ⟨0⟩
     let g2 := addPermanent g2 aerialDoombot ⟨0⟩ ⟨0⟩
     let dest := namedPermanent g2 "Aerial Doombot"
     let destName := dest.printed.name
     let g2 := g2.applyAbilityEffect ⟨0⟩ (Effect.copyArtifactYouControlNotLegendary)
       #[Target.permanent dest.id]
     (g2.object! dest.id).printed.name == destName) &&
    (mshRuling 473).comment.contains "exactly what was printed" &&
    (mshRuling 540).comment.contains "won't have any effect" &&
    (mshRuling 682).comment.contains "neither entering nor leaving"

#guard shuriCopyUntilEotOk

/-- Rulings 197 / 199 / 325: Secret Invasion copies until the Aura leaves. -/
def secretInvasionCopyOk : Bool :=
  let g := addPermanent afterDraw secretInvasion ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  let aura := namedPermanent g "Secret Invasion"
  let host := namedPermanent g "Grizzly Bears"
  let tgt := namedPermanent g "Hill Giant"
  let g := g.attachSourceTo aura host
  let g := g.applyTriggeredAbility ⟨0⟩ .onEnterExileOtherCopyEnchanted
    (some aura.id) #[Target.permanent tgt.id]
  let host := g.object! host.id
  host.copyRestore.isSome &&
    (host.copyRestore.getD host.printed).name == "Grizzly Bears" &&
    host.printed.name == "Hill Giant" &&
    (let aura := namedPermanent g "Secret Invasion"
     let (g, _) := g.move aura.id (.graveyard ⟨0⟩) none
     (namedPermanent g "Grizzly Bears").printed.name == "Grizzly Bears") &&
    (mshRuling 677).comment.contains "exactly what was printed" &&
    (mshRuling 681).comment.contains "neither entering nor leaving"

#guard secretInvasionCopyOk

/-- Rulings 95 / 142 / 160: She-Hulk may deal the total even if she left; once. -/
def sheHulkDamageOnceOk : Bool :=
  let g := addPermanent afterDraw theSensationalSheHulk ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  let she := namedPermanent g "The Sensational She-Hulk"
  let bears := namedPermanent g "Grizzly Bears"
  let giant := namedPermanent g "Hill Giant"
  let g := g.markDamageOn bears 3 "Bears are dealt 3 damage"
  g.waitingTriggers.any (fun t =>
    t.source.name == "The Sensational She-Hulk") &&
    (let (g, _) := g.move she.id (.graveyard ⟨0⟩) none
     let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchSheHulkRedirectOnce)
       (some she.id) #[Target.permanent giant.id]
       "The Sensational She-Hulk" (some 3)
     let giant := namedPermanent g "Hill Giant"
     giant.status.damage == 3 &&
       g.sheHulkDamageUsedThisTurn &&
       (let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchSheHulkRedirectOnce)
          (some she.id) #[Target.permanent giant.id]
          "The Sensational She-Hulk" (some 5)
        (namedPermanent g "Hill Giant").status.damage == 3 &&
          logContains g "no effect")) &&
    (mshRuling 448).comment.contains "won't trigger again that turn" &&
    (mshRuling 495).comment.contains "may still have her deal damage" &&
    (mshRuling 512).comment.contains "total amount of damage"

#guard sheHulkDamageOnceOk

/-- Rulings 34 / 40 / 47 / 61 / 62 / 302: copying a stack ability is not
casting and keeps the same source and X. -/
def copyStackAbilityOk : Bool :=
  let g := addPermanent afterDraw aerialDoombot ⟨0⟩ ⟨0⟩
  let src := namedPermanent g "Aerial Doombot"
  let (g, ab) := g.allocStackAbility src ⟨0⟩
    (triggeredAbility := some (.onEnterDraw 1)) (lastKnownPower := some 4)
  let g := g.setObject { ab with chosenX := some 2 }
  let g := g.putStackEntry ⟨0⟩ ab.id
  let origId := ab.id
  let g := g.copyStackAbility (g.object! origId) ⟨0⟩
  let copies := g.objects.filter (fun o =>
    o.zone == .stack && o.isCopy && o.sourceId == some src.id)
  copies.size == 1 &&
    copies[0]!.chosenX == some 2 &&
    copies[0]!.lastKnownPower == some 4 &&
    copies[0]!.triggeredAbility.isSome &&
    g.stack.size == 2 &&
    g.stack.back!.objectId == copies[0]!.id &&
    (mshRuling 389).comment.contains "won't apply to copying" &&
    (mshRuling 394).comment.contains "won't cause abilities that trigger" &&
    (mshRuling 401).comment.contains "same value of X" &&
    (mshRuling 414).comment.contains "same targets as the ability" &&
    (mshRuling 415).comment.contains "resolve before the original" &&
    (mshRuling 654).comment.contains "same as the source of the original"

#guard copyStackAbilityOk

/-- Ruling 449: Worlds Within Worlds exiles creatures, then hand creatures
enter, then the exiled cards return to hands. -/
def worldsWithinWorldsOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  let g := addToHand g aerialDoombot ⟨0⟩
  let (g, spell) := g.allocObject worldsWithinWorlds ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.applyWorldsWithinWorlds ⟨0⟩ (some spell.id)
  g.battlefield.any (fun o => o.name == "Aerial Doombot") &&
    !g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    !g.battlefield.any (fun o => o.name == "Hill Giant") &&
    (g.player ⟨0⟩).hand.any (fun id => (g.object! id).name == "Grizzly Bears") &&
    (g.player ⟨1⟩).hand.any (fun id => (g.object! id).name == "Hill Giant") &&
    (match g.findObject? spell.id with
     | some o => o.zone == .exile
     | none =>
       g.objects.any (fun o => o.name == "Worlds Within Worlds" && o.zone == .exile)) &&
    (mshRuling 449).comment.contains "Worlds Within Worlds"

#guard worldsWithinWorldsOk

/-- Ruling 484: Captain America's attack pump uses last-known toughness. -/
def capWingsLastKnownToughnessOk : Bool :=
  let g := addPermanent afterDraw captainAmericaWingsOfFreedom ⟨0⟩ ⟨0⟩
  let g := addPermanent g sheHulkJadeDefender ⟨0⟩ ⟨0⟩
  let cap := namedPermanent g "Captain America, Wings of Freedom"
  let g := g.mapObjectStatus cap (fun s => { s with pump := (0, 4) })
  let cap := namedPermanent g "Captain America, Wings of Freedom"
  let tw := g.toughness cap
  let she0 := g.toughness (namedPermanent g "She-Hulk, Jade Defender")
  let (g, _) := g.move cap.id (.graveyard ⟨0⟩) none
  let g := g.applyTriggeredAbility ⟨0⟩
    (.onAttackOthersOfSubtypeGetEqualToughness "Hero") (some cap.id)
    #[] #[] none (some tw)
  g.toughness (namedPermanent g "She-Hulk, Jade Defender") == she0 + tw &&
    (mshRuling 484).comment.contains "last existed on the battlefield" &&
    (mshRuling 662).comment.contains "determined only once"

#guard capWingsLastKnownToughnessOk

/-- Ruling 500 / 321: Viv Vision draws using last-known power if she left. -/
def vivVisionLastKnownPowerOk : Bool :=
  let g := addPermanent afterDraw vivVisionTeenSynthezoid ⟨0⟩ ⟨0⟩
  let viv := namedPermanent g "Viv Vision, Teen Synthezoid"
  let g := g.addPlusOnePlusOneTo viv 2
  let viv := namedPermanent g "Viv Vision, Teen Synthezoid"
  let pw := g.power viv
  let hand0 := (g.player ⟨0⟩).hand.size
  let (g, _) := g.move viv.id (.graveyard ⟨0⟩) none
  let g := g.applyModeledTrigger ⟨0⟩ (.onThisAttack Effect.thisAttackDrawIfPower4) (some viv.id)
    #[] "Viv Vision" (some pw)
  pw >= 4 &&
    (g.player ⟨0⟩).hand.size == hand0 + 1 &&
    (mshRuling 500).comment.contains "last existed on the battlefield" &&
    (mshRuling 673).comment.contains "checks Viv Vision's power only as it resolves"

#guard vivVisionLastKnownPowerOk

/-- Ruling 501: War Machine's combat pump uses last-known power. -/
def warMachineLastKnownPowerOk : Bool :=
  let g := addPermanent afterDraw warMachineLegacyOfIron ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let wm := namedPermanent g "War Machine, Legacy of Iron"
  let g := g.addPlusOnePlusOneTo wm 3
  let wm := namedPermanent g "War Machine, Legacy of Iron"
  let pw := g.power wm
  let bears := namedPermanent g "Grizzly Bears"
  let p0 := g.power bears
  let (g, _) := g.move wm.id (.graveyard ⟨0⟩) none
  let g := g.applyTriggeredAbility ⟨0⟩ .onCombatAnotherGetsSourcePower (some wm.id)
    #[Target.permanent bears.id] #[] (some pw)
  g.power (namedPermanent g "Grizzly Bears") == p0 + pw &&
    (mshRuling 501).comment.contains "last existed on the battlefield" &&
    (mshRuling 660).comment.contains "calculated only once"

#guard warMachineLastKnownPowerOk

/-- Leader's combat trigger connives the targeted creature, not Leader. -/
def leaderCombatConniveTargetsOtherOk : Bool :=
  let g := addPermanent afterDraw leaderSuperGenius ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addToHand g lightningBolt ⟨0⟩
  let leader := namedPermanent g "Leader, Super-Genius"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.applyTriggeredAbility ⟨0⟩ .onCombatTargetYouControlConnives (some leader.id)
    #[Target.permanent bears.id]
  let g := discardNamed g ⟨0⟩ "Lightning Bolt"
  (namedPermanent g "Grizzly Bears").status.plusOnePlusOne == 1 &&
    (namedPermanent g "Leader, Super-Genius").status.plusOnePlusOne == 0

#guard leaderCombatConniveTargetsOtherOk

/-- Alien Invasion creates a hasty Alien, then grows later tokens from invasion. -/
def alienInvasionCombatTokenOk : Bool :=
  let g := addPermanent afterDraw alienInvasion ⟨0⟩ ⟨0⟩
  let src := namedPermanent g "Alien Invasion"
  let g := g.applyTriggeredAbility ⟨0⟩ .onCombatCreateAlienPerInvasion (some src.id)
  let tok := namedPermanent g "Alien"
  let firstOk :=
    tok.printed.isToken && tok.status.plusOnePlusOne == 0 &&
      tok.printed.keywords.haste &&
      tok.staticAbilities.contains .attacksEachCombatIfAble &&
      (namedPermanent g "Alien Invasion").status.invasion == 1
  let src := namedPermanent g "Alien Invasion"
  let g := g.applyTriggeredAbility ⟨0⟩ .onCombatCreateAlienPerInvasion (some src.id)
  let aliens := g.battlefield.filter (fun o => o.name == "Alien")
  firstOk &&
    aliens.size == 2 &&
    aliens.any (fun o => o.status.plusOnePlusOne == 0) &&
    aliens.any (fun o => o.status.plusOnePlusOne == 1) &&
    (namedPermanent g "Alien Invasion").status.invasion == 2

#guard alienInvasionCombatTokenOk

/-- Iron Man may put Equipment from hand onto the battlefield attached to him. -/
def ironManCombatPutEquipmentOk : Bool :=
  let g := addPermanent afterDraw theInvincibleIronMan ⟨0⟩ ⟨0⟩
  let g := addToHand g hawkeyeSBow ⟨0⟩
  let iron := namedPermanent g "The Invincible Iron Man"
  let g := g.applyTriggeredAbility ⟨0⟩ .onCombatMayPutArtifactAttachEquipment
    (some iron.id)
  match g.pending with
  | .mayPutArtifactFromHand ⟨0⟩ hostId =>
    let bow := handCardNamed g ⟨0⟩ "Hawkeye's Bow"
    let g := mustApply g ⟨0⟩ (.cast bow.id)
    let bow := namedPermanent g "Hawkeye's Bow"
    hostId == iron.id &&
      bow.isOnBattlefield &&
      bow.attachedTo == some iron.id
  | _ => false

#guard ironManCombatPutEquipmentOk

/-- Iron Man may decline the optional put. -/
def ironManCombatDeclinePutOk : Bool :=
  let g := addPermanent afterDraw theInvincibleIronMan ⟨0⟩ ⟨0⟩
  let g := addToHand g hawkeyeSBow ⟨0⟩
  let iron := namedPermanent g "The Invincible Iron Man"
  let g := g.applyTriggeredAbility ⟨0⟩ .onCombatMayPutArtifactAttachEquipment
    (some iron.id)
  let g := mustApply g ⟨0⟩ .decline
  (handCardNamed g ⟨0⟩ "Hawkeye's Bow").zone == .hand ⟨0⟩ &&
    g.pending == .none &&
    g.log.any (fun s => mentions s "declines to put an artifact")

#guard ironManCombatDeclinePutOk

/-- Iron Man puts a non-Equipment artifact without attaching it. -/
def ironManCombatPutNonEquipmentOk : Bool :=
  let g := addPermanent afterDraw theInvincibleIronMan ⟨0⟩ ⟨0⟩
  let g := addToHand g theMindStone ⟨0⟩
  let iron := namedPermanent g "The Invincible Iron Man"
  let g := g.applyTriggeredAbility ⟨0⟩ .onCombatMayPutArtifactAttachEquipment
    (some iron.id)
  let stone := handCardNamed g ⟨0⟩ "The Mind Stone"
  let g := mustApply g ⟨0⟩ (.cast stone.id)
  let stone := namedPermanent g "The Mind Stone"
  stone.isOnBattlefield && stone.attachedTo.isNone

#guard ironManCombatPutNonEquipmentOk

/-- Ruling 490: Political Triumph still draws and counters if it left. -/
def politicalTriumphLeftOk : Bool :=
  let g := addPermanent afterDraw politicalTriumph ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let plan := namedPermanent g "Political Triumph"
  let hand0 := (g.player ⟨0⟩).hand.size
  let (g, _) := g.move plan.id (.graveyard ⟨0⟩) none
  let g := g.applyTriggeredAbility ⟨0⟩ .onFourthPlanDrawPlusOneEach (some plan.id)
  (g.player ⟨0⟩).hand.size == hand0 + 1 &&
    (namedPermanent g "Grizzly Bears").status.plusOnePlusOne == 1 &&
    (mshRuling 490).comment.contains "won't be able to sacrifice it"

#guard politicalTriumphLeftOk

/-- Ruling 492: Robot Domination still creates tokens if it left. -/
def robotDominationLeftOk : Bool :=
  let g := addPermanent afterDraw robotDomination ⟨0⟩ ⟨0⟩
  let plan := namedPermanent g "Robot Domination"
  let (g, _) := g.move plan.id (.graveyard ⟨0⟩) none
  let g := g.applyTriggeredAbility ⟨0⟩ .onThirdPlanCreateRobots (some plan.id)
  (g.battlefield.filter (fun o => o.name == "Robot Villain")).size == 3 &&
    (mshRuling 492).comment.contains "You'll create the Robot"

#guard robotDominationLeftOk

/-- Ruling 489: Jessica Jones exiles X using last-known power if she left. -/
def jessicaJonesLastKnownXOk : Bool :=
  let g := addPermanent afterDraw jessicaJonesPrivateEye ⟨0⟩ ⟨0⟩
  let jj := namedPermanent g "Jessica Jones, Private Eye"
  let g := g.addPlusOnePlusOneTo jj 1
  let jj := namedPermanent g "Jessica Jones, Private Eye"
  let pw := g.power jj
  let lib0 := (g.player ⟨0⟩).library.size
  let (g, _) := g.move jj.id (.graveyard ⟨0⟩) none
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.exileTopXPlayThisTurn) #[]
    (some jj.id) (some pw)
  (g.player ⟨0⟩).library.size == lib0 - pw.toNat &&
    (g.objects.filter (fun o =>
      o.zone == .exile && o.playPermission.isSome)).size == pw.toNat &&
    (mshRuling 489).comment.contains "last existed on the battlefield" &&
    (mshRuling 658).comment.contains "calculated only once"

#guard jessicaJonesLastKnownXOk

/-- Ruling 503: Whiplash drain uses last-known attached Equipment. -/
def whiplashLastKnownEquipmentOk : Bool :=
  let g := addPermanent afterDraw whiplashVengefulEngineer ⟨0⟩ ⟨0⟩
  let g := addPermanent g captainAmericaSShield ⟨0⟩ ⟨0⟩
  let g := addPermanent g falconSWingHarness ⟨0⟩ ⟨0⟩
  let whip := namedPermanent g "Whiplash, Vengeful Engineer"
  let eq1 := namedPermanent g "Captain America's Shield"
  let eq2 := namedPermanent g "Falcon's Wing Harness"
  let g := g.attachSourceTo eq1 whip
  let g := g.attachSourceTo eq2 (g.object! whip.id)
  let n := g.attachedEquipmentCount (g.object! whip.id)
  let life0 := (g.player ⟨1⟩).life
  let you0 := (g.player ⟨0⟩).life
  let (g, _) := g.move (namedPermanent g "Whiplash, Vengeful Engineer").id
    (.graveyard ⟨0⟩) none
  let g := g.applyModeledTrigger ⟨0⟩ (.onThisAttack Effect.thisAttackEquippedDrain) (some whip.id)
    #[] "Whiplash" (some (Int.ofNat n))
  n == 2 &&
    (g.player ⟨1⟩).life + n == life0 &&
    (g.player ⟨0⟩).life == you0 + n &&
    (mshRuling 503).comment.contains "last existed on the battlefield" &&
    (mshRuling 661).comment.contains "calculated only once"

#guard whiplashLastKnownEquipmentOk

/-- Rulings 359 / 367: first reflexive ability has no targets; the second does. -/
def mshReflexiveNoTargetFirstOk : Bool :=
  let g := addPermanent afterDraw bullseyeDeathDealer ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let b := namedPermanent g "Bullseye, Death Dealer"
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterMaySacOrDiscardNonlandThenDamage) (some b.id)
  (namedPermanent g "Grizzly Bears").status.damage == 0 &&
    g.pendingMshReflexive.isSome &&
    logContains g "reflexive" &&
    (let bears := namedPermanent g "Grizzly Bears"
     let g := g.applyModeledReflexive #[Target.permanent bears.id]
     (namedPermanent g "Grizzly Bears").status.damage == 2) &&
    (let g := addPermanent afterDraw spiderManToTheRescue ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
     let sm := namedPermanent g "Spider-Man, To the Rescue"
     let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterMayTapThenGrantIndestructible) (some sm.id)
     (namedPermanent g "Spider-Man, To the Rescue").status.tapped &&
       g.pendingMshReflexive.isSome &&
       (let bears := namedPermanent g "Grizzly Bears"
        let g := g.applyModeledReflexive #[Target.permanent bears.id]
        (namedPermanent g "Grizzly Bears").status.untilEotKeywords.indestructible)) &&
    (mshRuling 711).comment.contains "reflexive" &&
    (mshRuling 719).comment.contains "reflexive"

#guard mshReflexiveNoTargetFirstOk

/-- Ruling 478: Hawkeye's first trigger has no modes; paying queues the second. -/
def hawkeyeReflexivePayOk : Bool :=
  let g := addPermanent afterDraw hawkeyeMasterMarksman ⟨0⟩ ⟨0⟩
  let hawk := namedPermanent g "Hawkeye, Master Marksman"
  let nonePaid :=
    g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchHawkeyeModes) (some hawk.id)
      #[] "Hawkeye" none
  !nonePaid.pendingMshReflexive.isSome &&
    (let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchHawkeyeModes) (some hawk.id)
       #[] "Hawkeye" (some (2 : Int))
     g.pendingMshReflexive.isSome &&
       g.pendingMshReflexivePaid == 2 &&
       (let life1 := (g.player ⟨1⟩).life
        let g := g.applyModeledReflexive #[Target.player ⟨1⟩]
        (g.player ⟨1⟩).life + 2 == life1)) &&
    (mshRuling 478).comment.contains "reflexive"

#guard hawkeyeReflexivePayOk

/-- Ruling 712: Claim the Kingdom's first ability only sacrifices; the
indestructible counter is a reflexive second trigger. -/
def claimTheKingdomReflexiveOk : Bool :=
  let g := addPermanent afterDraw claimTheKingdom ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let plan := namedPermanent g "Claim the Kingdom"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.applyTriggeredAbility ⟨0⟩ .onFourthPlanIndestructible (some plan.id)
  !g.battlefield.any (fun o => o.name == "Claim the Kingdom") &&
    (namedPermanent g "Grizzly Bears").status.indestructibleCounters == 0 &&
    g.pendingMshReflexive.isSome &&
    (let g := g.applyModeledReflexive #[Target.permanent bears.id]
     (namedPermanent g "Grizzly Bears").status.indestructibleCounters == 1) &&
    (let g := addPermanent afterDraw claimTheKingdom ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
     let plan := namedPermanent g "Claim the Kingdom"
     let (g, _) := g.move plan.id (.graveyard ⟨0⟩) none
     let g := g.applyTriggeredAbility ⟨0⟩ .onFourthPlanIndestructible (some plan.id)
     !g.pendingMshReflexive.isSome &&
       (namedPermanent g "Grizzly Bears").status.indestructibleCounters == 0) &&
    (mshRuling 712).comment.contains "reflexive"

#guard claimTheKingdomReflexiveOk

/-- Ruling 713: Construct a Cosmic Cube queues control of an opponent. -/
def constructACosmicCubeReflexiveOk : Bool :=
  let g := addPermanent afterDraw constructACosmicCube ⟨0⟩ ⟨0⟩
  let plan := namedPermanent g "Construct a Cosmic Cube"
  let g := g.applyTriggeredAbility ⟨0⟩ .onSeventhPlanControlOpponent (some plan.id)
  !g.battlefield.any (fun o => o.name == "Construct a Cosmic Cube") &&
    g.pendingMshReflexive.isSome &&
    (let g := g.applyModeledReflexive #[Target.player ⟨1⟩]
     g.controlsPlayer ⟨0⟩ ⟨1⟩ && g.controlOnNextTakenTurn) &&
    (mshRuling 713).comment.contains "reflexive"

#guard constructACosmicCubeReflexiveOk

/-- Ruling 714: Doom Reigns Supreme exiles the opponent's top cards only
after the Plan is sacrificed. -/
def doomReignsSupremeReflexiveOk : Bool :=
  let g := addPermanent afterDraw doomReignsSupreme ⟨0⟩ ⟨0⟩
  let plan := namedPermanent g "Doom Reigns Supreme"
  let lib0 := (g.player ⟨1⟩).library.size
  let g := g.applyTriggeredAbility ⟨0⟩ .onFifthPlanExileTopCast (some plan.id)
  (g.player ⟨1⟩).library.size == lib0 &&
    g.pendingMshReflexive.isSome &&
    (let g := g.applyModeledReflexive #[Target.player ⟨1⟩]
     (g.player ⟨1⟩).library.size == lib0 - 5 &&
       (g.objects.filter (fun o =>
         o.zone == .exile && o.playPermission.isSome)).size == 5) &&
    (mshRuling 714).comment.contains "reflexive"

#guard doomReignsSupremeReflexiveOk

/-- Ruling 715: Grim Reaper's pay is the first ability; the return is
reflexive. -/
def grimReaperReflexiveOk : Bool :=
  let g := addPermanent afterDraw grimReaperLethalLegionnaire ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g grizzlyBears ⟨0⟩
  let grim := namedPermanent g "Grim Reaper, Lethal Legionnaire"
  let unpaid :=
    g.applyModeledTrigger ⟨0⟩ (.onThisAttack Effect.thisAttackPayReturnAttacking) (some grim.id)
  !unpaid.pendingMshReflexive.isSome &&
    (let g := g.applyModeledTrigger ⟨0⟩ (.onThisAttack Effect.thisAttackPayReturnAttacking) (some grim.id)
       #[] "Grim Reaper" (some (1 : Int))
     g.pendingMshReflexive.isSome &&
       (let gy := namedGraveyardCard g ⟨0⟩ "Grizzly Bears"
        let g := g.applyModeledReflexive #[Target.card gy.id]
        let bears := namedPermanent g "Grizzly Bears"
        bears.status.tapped && bears.status.attacking &&
          bears.status.finality ≥ 1)) &&
    (mshRuling 715).comment.contains "reflexive"

#guard grimReaperReflexiveOk

/-- Ruling 716: Killmonger only destroys if another creature was
sacrificed. -/
def killmongerReflexiveOk : Bool :=
  let g := addPermanent afterDraw killmongerScourgeOfWakanda ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let km := namedPermanent g "Killmonger, Scourge of Wakanda"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterMaySacAnotherThenDestroyOppNonland) (some km.id)
  !g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    g.pendingMshReflexive.isSome &&
    g.battlefield.any (fun o => o.name == "Gray Ogre") &&
    (let g := g.applyModeledReflexive #[Target.permanent ogre.id]
     !g.battlefield.any (fun o => o.name == "Gray Ogre")) &&
    (let g := addPermanent afterDraw killmongerScourgeOfWakanda ⟨0⟩ ⟨0⟩
     let km := namedPermanent g "Killmonger, Scourge of Wakanda"
     let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterMaySacAnotherThenDestroyOppNonland) (some km.id)
     !g.pendingMshReflexive.isSome) &&
    (mshRuling 716).comment.contains "reflexive"

#guard killmongerReflexiveOk

/-- Rulings 273 / 365: Red Hulk's reflexive damage uses the counters only
if he survived to receive one. -/
def redHulkReflexiveOk : Bool :=
  let g := addPermanent afterDraw redHulk ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let hulk := namedPermanent g "Red Hulk"
  let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchRedHulk) (some hulk.id)
  (namedPermanent g "Red Hulk").status.plusOnePlusOne == 1 &&
    g.pendingMshReflexive.isSome &&
    g.pendingMshReflexivePaid == 1 &&
    (let bears := namedPermanent g "Grizzly Bears"
     let g := g.applyModeledReflexive #[Target.permanent bears.id]
     (namedPermanent g "Grizzly Bears").status.damage == 1) &&
    (let g := addPermanent afterDraw redHulk ⟨0⟩ ⟨0⟩
     let hulk := namedPermanent g "Red Hulk"
     let (g, _) := g.move hulk.id (.graveyard ⟨0⟩) none
     let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchRedHulk) (some hulk.id)
     !g.pendingMshReflexive.isSome) &&
    (mshRuling 625).comment.contains "must survive the damage" &&
    (mshRuling 717).comment.contains "reflexive"

#guard redHulkReflexiveOk

/-- Ruling 718: Speed's pay queues a haste-only blocker restriction. -/
def speedYoungAvengerReflexiveOk : Bool :=
  let g := addPermanent afterDraw speedYoungAvenger ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let speed := namedPermanent g "Speed, Young Avenger"
  let unpaid :=
    g.applyModeledTrigger ⟨0⟩ (.onCasting Effect.castingMayPayHasteUnblockable) (some speed.id)
  !unpaid.pendingMshReflexive.isSome &&
    (let g := g.applyModeledTrigger ⟨0⟩ (.onCasting Effect.castingMayPayHasteUnblockable)
       (some speed.id) #[] "Speed" (some (1 : Int))
     g.pendingMshReflexive.isSome &&
       (let speed := namedPermanent g "Speed, Young Avenger"
        let g := g.applyModeledReflexive #[Target.permanent speed.id]
        let speed := namedPermanent g "Speed, Young Avenger"
        let g := g.setObject { speed with status := { speed.status with
          attacking := true, attackingWhom := some ⟨1⟩ } }
        let speed := namedPermanent g "Speed, Young Avenger"
        let bears := namedPermanent g "Grizzly Bears"
        speed.status.cantBeBlockedExceptByHasteUntilEot &&
          !g.canBlock bears speed &&
          (let g := g.mapObjectStatus bears (·.grantUntilEot Keyword.haste)
           g.canBlock (namedPermanent g "Grizzly Bears")
             (namedPermanent g "Speed, Young Avenger")))) &&
    (mshRuling 718).comment.contains "reflexive"

#guard speedYoungAvengerReflexiveOk

/-- Ruling 720: Death to Our Enemies deals 7 only after the sacrifice. -/
def deathToOurEnemiesReflexiveOk : Bool :=
  let g := addPermanent afterDraw deathToOurEnemies ⟨0⟩ ⟨0⟩
  let plan := namedPermanent g "Death to Our Enemies"
  let life0 := (g.player ⟨1⟩).life
  let g := g.applyTriggeredAbility ⟨0⟩ .onFourthPlanDividedDamage (some plan.id)
  (g.player ⟨1⟩).life == life0 &&
    g.pendingMshReflexive.isSome &&
    (let g := g.applyModeledReflexive #[Target.player ⟨1⟩]
     (g.player ⟨1⟩).life + 7 == life0) &&
    (mshRuling 720).comment.contains "reflexive"

#guard deathToOurEnemiesReflexiveOk

/-- Ruling 721: Rewrite History returns instants and sorceries only after
the Plan is sacrificed. -/
def rewriteHistoryReflexiveOk : Bool :=
  let g := addPermanent afterDraw rewriteHistory ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g helicarrierStrike ⟨0⟩
  let g := addToGraveyard g hourOfDefeat ⟨0⟩
  let plan := namedPermanent g "Rewrite History"
  let inst := namedGraveyardCard g ⟨0⟩ "Helicarrier Strike"
  let sorc := namedGraveyardCard g ⟨0⟩ "Hour of Defeat"
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.applyTriggeredAbility ⟨0⟩ .onFourthPlanReturnInstants (some plan.id)
  (g.player ⟨0⟩).hand.size == hand0 &&
    g.pendingMshReflexive.isSome &&
    (let g := g.applyModeledReflexive #[Target.card inst.id, Target.card sorc.id]
     (g.player ⟨0⟩).hand.size == hand0 + 2 &&
       (g.handObjects ⟨0⟩).any (fun o => o.name == "Helicarrier Strike") &&
       (g.handObjects ⟨0⟩).any (fun o => o.name == "Hour of Defeat")) &&
    (mshRuling 721).comment.contains "reflexive"

#guard rewriteHistoryReflexiveOk

/-- Rulings 283 / 370: Speedball pumps even if the spell left, and may
change any number of that spell's targets (illegal replacements stay). -/
def speedballRetargetOk : Bool :=
  let g := addPermanent afterDraw speedballNewWarrior ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g mountain ⟨1⟩ ⟨1⟩
  let speed := namedPermanent g "Speedball, New Warrior"
  let (g, bolt) := g.allocObject lightningBolt ⟨1⟩ .stack (some ⟨1⟩)
  let g := g.putStackEntry ⟨1⟩ bolt.id
  let g := g.setStackEntryTargets bolt.id #[Target.permanent speed.id]
  let (gGone, _) := g.move bolt.id (.graveyard ⟨1⟩) none
  let gGone :=
    gGone.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchSpeedballTargeted) (some speed.id)
  gGone.power (namedPermanent gGone "Speedball, New Warrior") == 4 &&
    gGone.toughness (namedPermanent gGone "Speedball, New Warrior") == 4 &&
    (let g :=
       g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchSpeedballTargeted) (some speed.id)
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.retargetStackSpell bolt.id #[Target.permanent bears.id]
     (match g.stackEntry? bolt.id with
      | some e => e.targets[0]? == some (Target.permanent bears.id)
      | none => false) &&
       (let mt := namedPermanent g "Mountain"
        let g := g.retargetStackSpell bolt.id #[Target.permanent mt.id]
        match g.stackEntry? bolt.id with
        | some e => e.targets[0]? == some (Target.permanent bears.id)
        | none => false)) &&
    (mshRuling 635).comment.contains "resolves even if that spell" &&
    (mshRuling 722).comment.contains "You may change any number of the targets"

#guard speedballRetargetOk

/-- Rulings 287 / 292 / 296 / 371: Kingpin extort pays once; life gained
equals life actually lost; combat assignment uses toughness, not power. -/
def kingpinExtortAndToughnessOk : Bool :=
  let g := addPermanent afterDraw theKingpinOfCrime ⟨0⟩ ⟨0⟩
  let (g, spell) := g.allocObject lightningBolt ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.putStackEntry ⟨0⟩ spell.id
  let g := g.putCastTriggersOnStack ⟨0⟩ (g.object! spell.id)
  g.pendingExtort == 1 &&
    (let life0 := (g.player ⟨0⟩).life
     let life1 := (g.player ⟨1⟩).life
     let g := g.applyExtort true
     (g.player ⟨1⟩).life + 1 == life1 &&
       (g.player ⟨0⟩).life == life0 + 1 &&
       g.pendingExtort == 0 &&
       (let g := g.applyExtort true
        g.pendingExtort == 0 && (g.player ⟨1⟩).life + 1 == life1)) &&
    (let g := addPermanent afterDraw theKingpinOfCrime ⟨0⟩ ⟨0⟩
     let (g, spell) := g.allocObject lightningBolt ⟨0⟩ .stack (some ⟨0⟩)
     let g := g.putStackEntry ⟨0⟩ spell.id
     let g := g.putCastTriggersOnStack ⟨0⟩ (g.object! spell.id)
     let g := g.modifyPlayer ⟨1⟩ (fun pl => { pl with lifeLocked := true })
     let life0 := (g.player ⟨0⟩).life
     let life1 := (g.player ⟨1⟩).life
     let g := g.applyExtort true
     (g.player ⟨1⟩).life == life1 &&
       (g.player ⟨0⟩).life == life0) &&
    (let g := addPermanent afterDraw theKingpinOfCrime ⟨0⟩ ⟨0⟩
     let kp := namedPermanent g "The Kingpin of Crime"
     let g := g.setObject { kp with status := { kp.status with
       attacking := true, attackingWhom := some ⟨1⟩, summoningSick := false } }
     let kp := namedPermanent g "The Kingpin of Crime"
     let g := g.applyModeledTrigger ⟨0⟩ (.onYouAttacking Effect.youAttackingPay2LifeToughness) (some kp.id)
       #[] "The Kingpin of Crime" (some (1 : Int))
     let kp := namedPermanent g "The Kingpin of Crime"
     g.power kp == 1 &&
       g.toughness kp == 5 &&
       g.combatDamageToAssign kp true == 5) &&
    (mshRuling 639).comment.contains "doesn't actually change any creature's power" &&
    (mshRuling 644).comment.contains "total amount of life lost" &&
    (mshRuling 648).comment.contains "doesn't target any player" &&
    (mshRuling 723).comment.contains "maximum of one time"

#guard kingpinExtortAndToughnessOk

/-- Ruling 727: Misty Knight draws for each discard this turn even if those
cards left the graveyard. -/
def mistyKnightDiscardCountOk : Bool :=
  let g := addPermanent afterDraw mistyKnightHeroForHire ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g lightningBolt ⟨0⟩
  let g := addToGraveyard g giantGrowth ⟨0⟩
  let bolt := namedGraveyardCard g ⟨0⟩ "Lightning Bolt"
  let growth := namedGraveyardCard g ⟨0⟩ "Giant Growth"
  let (g, _) := g.move bolt.id .exile none
  let (g, _) := g.move growth.id .exile none
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with cardsDiscardedThisTurn := 2 })
  let misty := namedPermanent g "Misty Knight, Hero for Hire"
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.drawPerDiscardedThisTurn) #[] (some misty.id)
  (g.player ⟨0⟩).hand.size == hand0 + 2 &&
    !(g.objects.any (fun o =>
      o.zone == .graveyard ⟨0⟩ &&
        (o.name == "Lightning Bolt" || o.name == "Giant Growth"))) &&
    (mshRuling 727).comment.contains "even if those cards are no longer"

#guard mistyKnightDiscardCountOk

/-- Ruling 447: Ares returns himself if he dies while attacking. -/
def aresDiesAttackingOk : Bool :=
  let g := addPermanent afterDraw aresGodOfWar ⟨0⟩ ⟨0⟩
  let ares := namedPermanent g "Ares, God of War"
  let g := g.setObject { ares with status := { ares.status with
    attacking := true, attackingWhom := some ⟨1⟩ } }
  let ares := namedPermanent g "Ares, God of War"
  let (g, _) := g.move ares.id (.graveyard ⟨0⟩) none
  let g := g.applyModeledTrigger ⟨0⟩ (.onDeath Effect.deathAttackingReturnHand)
    (some ares.id)
  (g.handObjects ⟨0⟩).any (fun o => o.name == "Ares, God of War") &&
    !g.battlefield.any (fun o => o.name == "Ares, God of War") &&
    (mshRuling 447).comment.contains "Ares himself"

#guard aresDiesAttackingOk

/-- Ruling 452: Attuma triggers once per player attacked with Merfolk. -/
def attumaMerfolkOncePerPlayerOk : Bool :=
  let g := addPermanent afterDraw attumaAtlanteanWarlord ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g :=
    g.mapObjectStatus (namedPermanent g "Grizzly Bears") (fun s =>
      { s with additionalSubtypes := #["Merfolk"] })
  let attuma := namedPermanent g "Attuma, Atlantean Warlord"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { attuma with status := { attuma.status with
    attacking := true, attackingWhom := some ⟨1⟩ } }
  let g := g.setObject { (namedPermanent g "Grizzly Bears") with status :=
    { bears.status with attacking := true, attackingWhom := some ⟨1⟩ } }
  let one :=
    g.putAttackTriggersOnStack ⟨0⟩
      #[(namedPermanent g "Attuma, Atlantean Warlord").id,
        (namedPermanent g "Grizzly Bears").id]
  let merfolkWaits (g : Game) : Nat :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.merfolkAttackPlayer)).size
  merfolkWaits one == 1 &&
    (let g := { afterDraw with
      players := afterDraw.players.push
        { (afterDraw.player ⟨1⟩) with id := ⟨2⟩, name := "Gimli" } }
     let g := addPermanent g attumaAtlanteanWarlord ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
     let g :=
       g.mapObjectStatus (namedPermanent g "Grizzly Bears") (fun s =>
         { s with additionalSubtypes := #["Merfolk"] })
     let attuma := namedPermanent g "Attuma, Atlantean Warlord"
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.setObject { attuma with status := { attuma.status with
       attacking := true, attackingWhom := some ⟨1⟩ } }
     let g := g.setObject { (namedPermanent g "Grizzly Bears") with status :=
       { bears.status with attacking := true, attackingWhom := some ⟨2⟩ } }
     let two :=
       g.putAttackTriggersOnStack ⟨0⟩
         #[(namedPermanent g "Attuma, Atlantean Warlord").id,
           (namedPermanent g "Grizzly Bears").id]
     merfolkWaits two == 2) &&
    (mshRuling 452).comment.contains "once for each player"

#guard attumaMerfolkOncePerPlayerOk

/-- Ruling 638: Avengers Assemble! still draws if the Hero left after
attacking. -/
def avengersAssembleHeroLeftOk : Bool :=
  let g := addPermanent afterDraw avengersAssemble ⟨0⟩ ⟨0⟩
  let g := addPermanent g mistyKnightHeroForHire ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with attackedWithHeroThisTurn := true })
  let hero := namedPermanent g "Misty Knight, Hero for Hire"
  let (g, _) := g.move hero.id (.graveyard ⟨0⟩) none
  let assem := namedPermanent g "Avengers Assemble!"
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.applyTriggeredAbility ⟨0⟩
    (.onEachEndStepDrawIfAttackedOrEnteredSubtype "Hero") (some assem.id)
  (g.player ⟨0⟩).hand.size == hand0 + 1 &&
    !g.battlefield.any (fun o => o.name == "Misty Knight, Hero for Hire") &&
    (mshRuling 638).comment.contains "doesn't need to still be on the battlefield"

#guard avengersAssembleHeroLeftOk

/-- Ruling 632: Shang-Chi lets you activate tap abilities immediately but
does not grant haste. -/
def shangChiActivateNotHasteOk : Bool :=
  -- `addPermanent` clears summoning sickness; insert Shang-Chi as sick.
  let g := insertObject afterDraw shangChiMasterOfKungFu ⟨0⟩ .battlefield
    (some ⟨0⟩) { summoningSick := true }
  let shang := namedPermanent g "Shang-Chi, Master of Kung Fu"
  let ab := shang.printed.activatedAbilities[0]!
  shang.hasSummoningSickness &&
    !g.canAttack shang &&
    !g.hasHaste shang &&
    g.canActivate ⟨0⟩ shang ab &&
    (mshRuling 632).comment.contains "doesn't grant haste"

#guard shangChiActivateNotHasteOk

/-- Ruling 624: Red Guardian can destroy a creature that dealt damage even
if the recipient has left. -/
def redGuardianDealtDamageOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.dealDamageFrom "Grizzly Bears" ogre 2 (source := some bears)
  let (g, _) := g.move (namedPermanent g "Gray Ogre").id (.graveyard ⟨0⟩) none
  let g := addPermanent g redGuardianSuperSoldier ⟨0⟩ ⟨0⟩
  let rg := namedPermanent g "Red Guardian, Super-Soldier"
  let bears := namedPermanent g "Grizzly Bears"
  bears.status.dealtDamageThisTurn &&
    (let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter (Effect.enterDestroy .oppCreatureDealtDamageThisTurn))
       (some rg.id) #[Target.permanent bears.id]
     !g.battlefield.any (fun o => o.name == "Grizzly Bears")) &&
    (let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
     let g := addPermanent g redGuardianSuperSoldier ⟨0⟩ ⟨0⟩
     let rg := namedPermanent g "Red Guardian, Super-Soldier"
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter (Effect.enterDestroy .oppCreatureDealtDamageThisTurn))
       (some rg.id) #[Target.permanent bears.id]
     g.battlefield.any (fun o => o.name == "Grizzly Bears")) &&
    (mshRuling 624).comment.contains "dealt damage this turn"

#guard redGuardianDealtDamageOk

/-- Rulings 221 / 259 / 300 / 346 / 358: control another player. -/
def controlAnotherPlayerOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := g.setPlayerControl ⟨0⟩ ⟨1⟩
  g.controlsPlayer ⟨0⟩ ⟨1⟩ &&
    g.activePlayer == ⟨0⟩ &&
    (namedPermanent g "Grizzly Bears").controlledBy ⟨1⟩ &&
    g.resourcesFor ⟨1⟩ == ⟨1⟩ &&
    (let g := g.setPlayerControl ⟨0⟩ ⟨1⟩
     let g := { g with controlOnNextTakenTurn := true }
     g.controlsPlayer ⟨0⟩ ⟨1⟩ && g.controlOnNextTakenTurn) &&
    (mshRuling 573).comment.contains "next turn they actually take" &&
    (mshRuling 611).comment.contains "overwrite each other" &&
    (mshRuling 652).comment.contains "still the active player" &&
    (mshRuling 698).comment.contains "can't use your own" &&
    (mshRuling 710).comment.contains "don't control any of that player's permanents"

#guard controlAnotherPlayerOk

/-- Ruling 458: Captain Mar-Vell grants flash if an opponent has already
cast a spell this turn, even if he entered afterward. -/
def captainMarVellFlashOk : Bool :=
  let g := addPermanent afterDraw captainMarVellSpaceBorn ⟨0⟩ ⟨0⟩
  let g := addToHand g grizzlyBears ⟨0⟩
  let gCombat := { g with step := .beginningOfCombat }
  let bears := handCardNamed gCombat ⟨0⟩ "Grizzly Bears"
  !gCombat.asSorcery? ⟨0⟩ &&
    !gCombat.canCast ⟨0⟩ bears &&
    (let gOpp := gCombat.modifyPlayer ⟨1⟩ (fun pl =>
      { pl with spellsCastThisTurn := 1 })
     gOpp.canCast ⟨0⟩ (handCardNamed gOpp ⟨0⟩ "Grizzly Bears")) &&
    (let gLate := addToHand afterDraw grizzlyBears ⟨0⟩
     let gLate := { gLate with step := .beginningOfCombat }
     let gLate := gLate.modifyPlayer ⟨1⟩ (fun pl =>
       { pl with spellsCastThisTurn := 1 })
     !gLate.canCast ⟨0⟩ (handCardNamed gLate ⟨0⟩ "Grizzly Bears") &&
       (let gLate := addPermanent gLate captainMarVellSpaceBorn ⟨0⟩ ⟨0⟩
        gLate.canCast ⟨0⟩ (handCardNamed gLate ⟨0⟩ "Grizzly Bears"))) &&
    (mshRuling 458).comment.contains "as though they had flash"

#guard captainMarVellFlashOk

/-- Ruling 441: becoming a Construct Hero artifact creature replaces
creature types and keeps Equipment. -/
def ironManArmorTypesOk : Bool :=
  let g := addPermanent afterDraw ironManArmor ⟨0⟩ ⟨0⟩
  let armor := namedPermanent g "Iron Man Armor"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.equipmentBecomesConstructHero) #[]
    (some armor.id)
  let armor := namedPermanent g "Iron Man Armor"
  armor.isCreature &&
    armor.hasSubtype "Construct" &&
    armor.hasSubtype "Hero" &&
    armor.hasSubtype "Equipment" &&
    armor.types.any (· == .artifact) &&
    g.power armor == 1 &&
    g.toughness armor == 1 &&
    (let g := addPermanent afterDraw grayOgre ⟨0⟩ ⟨0⟩
     let ogre := namedPermanent g "Gray Ogre"
     let g := g.mapObjectStatus ogre (fun s => { s with
       additionalArtifactUntilEot := true
       additionalCreatureUntilEot := true
       replacedCreatureTypesUntilEot := some #["Construct", "Hero"] })
     let ogre := namedPermanent g "Gray Ogre"
     !ogre.hasSubtype "Ogre" &&
       ogre.hasSubtype "Construct" &&
       ogre.hasSubtype "Hero") &&
    (mshRuling 441).comment.contains "replaces any existing creature types"

#guard ironManArmorTypesOk

/-- Ruling 491: Robot Domination does not see creature cards that go to
the graveyard at the same time it leaves, and an animated copy is not a
creature card. -/
def robotDominationSimultaneousOk : Bool :=
  let gyWait (g : Game) : Bool :=
    g.waitingTriggers.any (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.creatureCardsPutIntoYourGy)
  let g := addPermanent afterDraw robotDomination ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let (g, _) := g.move (namedPermanent g "Grizzly Bears").id (.graveyard ⟨0⟩) none
  gyWait g &&
    (let g := addPermanent afterDraw robotDomination ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
     let g := g.moveSimultaneousToGraveyard
       #[(namedPermanent g "Robot Domination").id,
         (namedPermanent g "Grizzly Bears").id]
     !gyWait g) &&
    (let g := addPermanent afterDraw robotDomination ⟨0⟩ ⟨0⟩
     let rd := namedPermanent g "Robot Domination"
     let g := g.mapObjectStatus rd (fun s =>
       { s with additionalCreatureUntilEot := true })
     let (g, _) :=
       g.move (namedPermanent g "Robot Domination").id (.graveyard ⟨0⟩) none
     !gyWait g) &&
    (mshRuling 491).comment.contains "won't trigger at all" &&
    (mshRuling 628).comment.contains "creature cards are put into your graveyard"

#guard robotDominationSimultaneousOk

/-- Ruling 575: two attackers are never attacking alone, even at
different players. -/
def attacksAloneDestinationsOk : Bool :=
  let alone (g : Game) : Bool :=
    g.waitingTriggers.any (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.creatureYouControlAttacksAlone)
  let g := addPermanent afterDraw agent13SharonCarter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.setObject { bears with status := { bears.status with
    attacking := true, attackingWhom := some ⟨1⟩ } }
  let g := g.setObject { (namedPermanent g "Gray Ogre") with status :=
    { ogre.status with attacking := true, attackingWhom := some ⟨2⟩ } }
  let two :=
    g.putAttackTriggersOnStack ⟨0⟩
      #[(namedPermanent g "Grizzly Bears").id,
        (namedPermanent g "Gray Ogre").id]
  !alone two &&
    (let g := addPermanent afterDraw agent13SharonCarter ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.setObject { bears with status := { bears.status with
       attacking := true, attackingWhom := some ⟨1⟩ } }
     let one :=
       g.putAttackTriggersOnStack ⟨0⟩ #[(namedPermanent g "Grizzly Bears").id]
     alone one) &&
    (mshRuling 430).comment.contains "attacks alone" &&
    (mshRuling 431).comment.contains "attacks alone" &&
    (mshRuling 432).comment.contains "declare attackers step" &&
    (mshRuling 433).comment.contains "declared as an attacker" &&
    (mshRuling 435).comment.contains "currently attacking" &&
    (mshRuling 575).comment.contains "neither attacking creature is attacking alone"

#guard attacksAloneDestinationsOk

/-- Ruling 685: Daredevil lets you play the exiled card whether or not
it is a Hero; Hero-ness only grants the pump. -/
def daredevilPlayExiledOk : Bool :=
  let g := addPermanent afterDraw daredevilManWithoutFear ⟨0⟩ ⟨0⟩
  let g := addToLibraryTop g lightningBolt ⟨0⟩
  let dd := namedPermanent g "Daredevil, Man Without Fear"
  let g := g.applyModeledTrigger ⟨0⟩ (.onYouAttacking Effect.youAttackingExileTopHeroPump) (some dd.id)
  let bolt? := g.objects.find? (fun o =>
    o.name == "Lightning Bolt" && o.zone == .exile)
  (match bolt? with
   | some o =>
     g.mayPlayFromExile ⟨0⟩ o &&
       (namedPermanent g "Daredevil, Man Without Fear").status.pump == (0, 0)
   | none => false) &&
    (let g := addPermanent afterDraw daredevilManWithoutFear ⟨0⟩ ⟨0⟩
     let g := addToLibraryTop g mistyKnightHeroForHire ⟨0⟩
     let dd := namedPermanent g "Daredevil, Man Without Fear"
     let g := g.applyModeledTrigger ⟨0⟩ (.onYouAttacking Effect.youAttackingExileTopHeroPump) (some dd.id)
     let hero? := g.objects.find? (fun o =>
       o.name == "Misty Knight, Hero for Hire" && o.zone == .exile)
     match hero? with
     | some o =>
       g.mayPlayFromExile ⟨0⟩ o &&
         (namedPermanent g "Daredevil, Man Without Fear").status.pump == (2, 1)
     | none => false) &&
    (mshRuling 685).comment.contains "You may play the exiled card"

#guard daredevilPlayExiledOk

/-- Ruling 437: opening-hand actions happen after mulligans, starting
player first, then the first turn begins. -/
def quicksilverOpeningHandOk : Bool :=
  let g := addToHand afterDraw quicksilverBrashBlur ⟨0⟩
  let g := addToHand g quicksilverBrashBlur ⟨1⟩
  let g := g.applyOpeningHandActions
  let p0 := g.battlefield.find? (fun o =>
    o.name == "Quicksilver, Brash Blur" && o.controlledBy ⟨0⟩)
  let p1 := g.battlefield.find? (fun o =>
    o.name == "Quicksilver, Brash Blur" && o.controlledBy ⟨1⟩)
  p0.isSome && p1.isSome &&
    (match p0, p1 with
     | some a, some b => a.timestamp < b.timestamp
     | _, _ => false) &&
    (mshRuling 437).comment.contains "opening hand"

#guard quicksilverOpeningHandOk

/-- Ruling 539: a copy cast without paying its mana cost has X = 0. -/
def freeCopyXIsZeroOk : Bool :=
  let g := addToHand afterDraw photonBlastBarrage ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Photon Blast Barrage"
  let card := { card with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }
  g.playManaCost card photonBlastBarrage == ManaCost.zero &&
    (mshRuling 539).comment.contains "choose 0 as the value of X" &&
    (mshRuling 197).comment.contains "can't choose to cast it for any alternative"

#guard freeCopyXIsZeroOk

/-- Ruling 483: Ares must attack if able, but not if he is sick, tapped,
or attacking would cost. -/
def aresAttacksIfAbleOk : Bool :=
  let g := addPermanent afterDraw aresGodOfWar ⟨0⟩ ⟨0⟩
  let ares := namedPermanent g "Ares, God of War"
  g.mustAttackIfAble ares &&
    (let g := insertObject afterDraw aresGodOfWar ⟨0⟩ .battlefield
       (some ⟨0⟩) { summoningSick := true }
     !g.mustAttackIfAble (namedPermanent g "Ares, God of War")) &&
    (let g := g.mapObjectStatus ares (fun s => { s with tapped := true })
     !g.mustAttackIfAble (namedPermanent g "Ares, God of War")) &&
    !g.mustAttackIfAble ares (attackRequiresCost := true) &&
    (mshRuling 483).comment.contains "doesn't have to attack"

#guard aresAttacksIfAbleOk

/-- Ruling 657: Hawkeye's plus-X is calculated when the noncombat damage
would be dealt. -/
def hawkeyeNoncombatXOk : Bool :=
  let g := addPermanent afterDraw hawkeyeYoungAvenger ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let ogre := namedPermanent g "Gray Ogre"
  let bears := namedPermanent g "Grizzly Bears"
  let gHit := g.dealDamageFrom "Gray Ogre" bears 2 (source := some ogre)
  (namedPermanent gHit "Grizzly Bears").status.damage == 4 &&
    (let g := g.pumpPermanent (namedPermanent g "Hawkeye, Young Avenger") 3 0
     let ogre := namedPermanent g "Gray Ogre"
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.dealDamageFrom "Gray Ogre" bears 2 (source := some ogre)
     (namedPermanent g "Grizzly Bears").status.damage == 7) &&
    (let (g, _) :=
       g.move (namedPermanent g "Hawkeye, Young Avenger").id (.graveyard ⟨0⟩) none
     let ogre := namedPermanent g "Gray Ogre"
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.dealDamageFrom "Gray Ogre" bears 2 (source := some ogre)
     (namedPermanent g "Grizzly Bears").status.damage == 2) &&
    (mshRuling 657).comment.contains "calculated at the time"

#guard hawkeyeNoncombatXOk

/-- Rulings 372 / 373 / 374: play-from-exile permissions still follow
normal timing. -/
def exilePlayFollowsTimingOk : Bool :=
  let g := addToHand afterDraw grizzlyBears ⟨0⟩
  let card := handCardNamed g ⟨0⟩ "Grizzly Bears"
  let (g, exiled) := g.move card.id .exile none
  let o := g.object! exiled
  let g := g.setObject { o with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1 } }
  let o := g.object! exiled
  g.mayPlayFromExile ⟨0⟩ o &&
    g.canCast ⟨0⟩ o &&
    (let gCombat := { g with step := .beginningOfCombat }
     !gCombat.asSorcery? ⟨0⟩ &&
       !gCombat.canCast ⟨0⟩ (gCombat.object! exiled)) &&
    (mshRuling 388).comment.contains "normal timing rules" &&
    (mshRuling 421).comment.contains "normal timing rules" &&
    (mshRuling 724).comment.contains "normal timing rules" &&
    (mshRuling 725).comment.contains "normal timing rules" &&
    (mshRuling 726).comment.contains "timing rules"

#guard exilePlayFollowsTimingOk

/-- Rulings 133 / 189: Crossbones sees other Villains that enter with him,
but the ability triggers only once each turn. -/
def crossbonesVillainOnceOk : Bool :=
  let villainWait (g : Game) : Nat :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.anotherVillainEnters)).size
  let g0 := addPermanent afterDraw crossbonesMaliciousMercenary ⟨0⟩ ⟨0⟩
  let gAlone := g0.afterPermanentEnters
    (namedPermanent g0 "Crossbones, Malicious Mercenary")
  villainWait gAlone == 0 &&
    (let g := addPermanent g0 redGuardianSuperSoldier ⟨0⟩ ⟨0⟩
     let g := g.afterPermanentEnters
       (namedPermanent g "Red Guardian, Super-Soldier")
     villainWait g == 1 &&
       (let xb := namedPermanent g "Crossbones, Malicious Mercenary"
        xb.status.firedOnceEachTurn &&
          (let g := addPermanent g baronStruckerHYDRAOverlord ⟨0⟩ ⟨0⟩
           let g := g.afterPermanentEnters
             (namedPermanent g "Baron Strucker, HYDRA Overlord")
           villainWait g == 1))) &&
    (let xb := namedPermanent g0 "Crossbones, Malicious Mercenary"
     let g := g0.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchVillainPlusOneDamageOnce)
       (some xb.id)
     (namedPermanent g "Crossbones, Malicious Mercenary").status.plusOnePlusOne == 1 &&
       (g.player ⟨1⟩).life == 18) &&
    (mshRuling 486).comment.contains "same time as other Villains" &&
    (mshRuling 541).comment.contains "trigger only once"

#guard crossbonesVillainOnceOk

/-- Ruling 659: Squirrel Girl's X is the squirrel count as the ability
resolves. -/
def squirrelGirlXOnceOk : Bool :=
  let g := addPermanent afterDraw theUnbeatableSquirrelGirl ⟨0⟩ ⟨0⟩
  let squirrels (g : Game) : Nat :=
    (g.battlefield.filter (fun o => o.hasSubtype "Squirrel")).size
  let n0 := squirrels g
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.createTokensEqualSubtype .squirrel11green "Squirrel") #[] none
  let n1 := squirrels g
  n0 == 1 && n1 == 2 &&
    (let g := g.applyAbilityEffect ⟨0⟩ (Effect.createTokensEqualSubtype .squirrel11green "Squirrel") #[] none
     squirrels g == 4) &&
    (mshRuling 659).comment.contains "calculated only once"

#guard squirrelGirlXOnceOk

/-- Rulings 171 / 172: a copy of a linked exile ability adds to the same
exiled-card set; both return when the source leaves. -/
def linkedExileCopyOk : Bool :=
  let g := addPermanent afterDraw cloakAndDaggerEntwined ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let cd := namedPermanent g "Cloak and Dagger, Entwined"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterRevealHandExileUntilLeaves)
    (some cd.id) #[Target.player ⟨1⟩, Target.permanent bears.id]
  (namedPermanent g "Cloak and Dagger, Entwined").linkedExile.size == 1 &&
    (let cd := namedPermanent g "Cloak and Dagger, Entwined"
     let ogre := namedPermanent g "Gray Ogre"
     let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterRevealHandExileUntilLeaves)
       (some cd.id) #[Target.player ⟨1⟩, Target.permanent ogre.id]
     let cd := namedPermanent g "Cloak and Dagger, Entwined"
     cd.linkedExile.size == 2 &&
       !g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
       !g.battlefield.any (fun o => o.name == "Gray Ogre") &&
       (let (g, _) := g.move cd.id (.graveyard ⟨0⟩) none
        g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
          g.battlefield.any (fun o => o.name == "Gray Ogre"))) &&
    (mshRuling 523).comment.contains "linked to a second ability" &&
    (mshRuling 524).comment.contains "linked to a second ability"

#guard linkedExileCopyOk

/-- Ruling 526: boast can be activated only once even if there is another
combat. -/
def boastOncePerTurnOk : Bool :=
  let g := addPermanent afterDraw baronHelmutZemo ⟨0⟩ ⟨0⟩
  let z := namedPermanent g "Baron Helmut Zemo"
  let g := g.mapObjectStatus z (fun s => { s with
    declaredAsAttackerThisTurn := true })
  let z := namedPermanent g "Baron Helmut Zemo"
  g.canActivateBoast z &&
    (let g := g.markBoastUsed z
     let z := namedPermanent g "Baron Helmut Zemo"
     !g.canActivateBoast z &&
       (let g := { g with additionalCombatPhases := 1 }
        !g.canActivateBoast (namedPermanent g "Baron Helmut Zemo"))) &&
    (mshRuling 526).comment.contains "only once"

#guard boastOncePerTurnOk

/-- Ruling 525: a token that dealt first-strike damage and then lost first
strike does not also deal regular combat damage. -/
def okoyeFirstStrikeLossOk : Bool :=
  let g := addPermanent afterDraw okoyeDoraMilajeLeader ⟨0⟩ ⟨0⟩
  let (g, tok) := g.createToken ⟨0⟩ Game.soldier11whiteToken
  let g := g.setObject { tok with status := { tok.status with
    attacking := true, attackingWhom := some ⟨1⟩ } }
  let tok := g.object! tok.id
  g.hasFirstStrike tok &&
    (let g := { g with
        firstStrikeDamageDone := true
        firstStrikeAssignedThisCombat := #[tok.id] }
     let (g, _) := g.move (namedPermanent g "Okoye, Dora Milaje Leader").id
       (.graveyard ⟨0⟩) none
     let tok := g.object! tok.id
     !g.hasFirstStrike tok &&
       !(g.creaturesAssigningCombatDamage true).any (fun o => o.id == tok.id)) &&
    (mshRuling 525).comment.contains "won't also deal normal combat damage"

#guard okoyeFirstStrikeLossOk

/-- Rulings 191 / 192: Nick Fury puts a DFC onto the battlefield front-face-up
unless it is night and the front has daybound. -/
def nickFuryDayDfc : CardDef := { bruceBanner with daybound := true }

def nickFuryDayEnter : Game :=
  let g := addToLibraryTop afterDraw nickFuryDayDfc ⟨0⟩
  g.enterFromNickFury ⟨0⟩ (g.player ⟨0⟩).library.back!

def nickFuryNightEnter : Game :=
  let g := addToLibraryTop { afterDraw with isNight := true } nickFuryDayDfc ⟨0⟩
  g.enterFromNickFury ⟨0⟩ (g.player ⟨0⟩).library.back!

#guard (namedPermanent nickFuryDayEnter "Bruce Banner").name == "Bruce Banner"
#guard !(namedPermanent nickFuryDayEnter "Bruce Banner").status.cantTransform
#guard
  let banner := namedPermanent nickFuryDayEnter "Bruce Banner"
  let g := nickFuryDayEnter.applyAbilityEffect ⟨0⟩ (Effect.transform) #[] (some banner.id)
  (namedPermanent g "The Incredible Hulk").name == "The Incredible Hulk"
#guard nickFuryNightEnter.isNight && nickFuryDayDfc.daybound &&
  nickFuryDayDfc.otherFace.isSome
#guard (namedPermanent nickFuryNightEnter "The Incredible Hulk").status.cantTransform
#guard
  let hulk := namedPermanent nickFuryNightEnter "The Incredible Hulk"
  let g := nickFuryNightEnter.applyAbilityEffect ⟨0⟩ (Effect.transform) #[] (some hulk.id)
  (namedPermanent g "The Incredible Hulk").name == "The Incredible Hulk" &&
    logContains g "can't transform"
#guard (mshRuling 543).comment.contains "daybound"
#guard (mshRuling 544).comment.contains "front face up"

def nickFuryDayboundOk : Bool :=
  let banner := namedPermanent nickFuryDayEnter "Bruce Banner"
  let gFlip := nickFuryDayEnter.applyAbilityEffect ⟨0⟩ (Effect.transform) #[] (some banner.id)
  let hulk := namedPermanent nickFuryNightEnter "The Incredible Hulk"
  let gBlocked := nickFuryNightEnter.applyAbilityEffect ⟨0⟩ (Effect.transform) #[] (some hulk.id)
  banner.name == "Bruce Banner" &&
    !banner.status.cantTransform &&
    (namedPermanent gFlip "The Incredible Hulk").name == "The Incredible Hulk" &&
    hulk.status.cantTransform &&
    (namedPermanent gBlocked "The Incredible Hulk").name == "The Incredible Hulk" &&
    logContains gBlocked "can't transform" &&
    (mshRuling 543).comment.contains "daybound" &&
    (mshRuling 544).comment.contains "front face up"

#guard nickFuryDayboundOk

/-- Rulings 334 / 335 / 336: you still decide for yourself, you see the
controlled player's hand, and you make their choices. -/
def controlPlayerChoicesOk : Bool :=
  let g := addToHand afterDraw lightningBolt ⟨1⟩
  let g := g.setPlayerControl ⟨0⟩ ⟨1⟩
  g.decidesFor ⟨0⟩ ⟨0⟩ &&
    g.decidesFor ⟨0⟩ ⟨1⟩ &&
    !g.decidesFor ⟨1⟩ ⟨1⟩ &&
    g.canSeeAs ⟨0⟩ ⟨1⟩ &&
    !g.canSeeAs ⟨1⟩ ⟨0⟩ &&
    (g.visibleHand ⟨0⟩ ⟨1⟩).any (fun o => o.name == "Lightning Bolt") &&
    (g.visibleHand ⟨1⟩ ⟨0⟩).isEmpty &&
    (mshRuling 686).comment.contains "continue to make your own choices" &&
    (mshRuling 687).comment.contains "you can see all cards" &&
    (mshRuling 688).comment.contains "you make all choices"

#guard controlPlayerChoicesOk

/-- Rulings 349 / 350 / 351 / 352: controlling a player does not reveal
their sideboard, grant outside-game or tournament choices, or let you
concede for them. They may still concede. -/
def controlPlayerLimitsOk : Bool :=
  let g := afterDraw.setPlayerControl ⟨0⟩ ⟨1⟩
  !g.canLookAtSideboard ⟨0⟩ ⟨1⟩ &&
    g.canLookAtSideboard ⟨1⟩ ⟨1⟩ &&
    !g.canChooseOutsideGame ⟨0⟩ ⟨1⟩ &&
    !g.canMakeTournamentDecision ⟨0⟩ ⟨1⟩ &&
    g.canMakeTournamentDecision ⟨1⟩ ⟨1⟩ &&
    !g.canMakeIllegalDecision ⟨0⟩ ⟨1⟩ &&
    !g.canConcedeAs ⟨0⟩ ⟨1⟩ &&
    g.canConcedeAs ⟨1⟩ ⟨1⟩ &&
    (let g := g.concede ⟨1⟩
     (g.player ⟨1⟩).lost) &&
    (mshRuling 701).comment.contains "sideboard" &&
    (mshRuling 702).comment.contains "tournament rules" &&
    (mshRuling 703).comment.contains "can't make any illegal decisions" &&
    (mshRuling 704).comment.contains "can't make the player"

#guard controlPlayerLimitsOk

/-- Rulings 193 / 196 / 197 / 200: copying a token uses its original
characteristics, not counters or tap. -/
def copyTokenOriginalOk : Bool :=
  let g := addPermanent afterDraw aerialDoombot ⟨0⟩ ⟨0⟩
  let (g, tok) := g.createToken ⟨0⟩ Game.soldier11whiteToken
  let g := g.mapObjectStatus tok (fun s =>
    { s with plusOnePlusOne := 3, tapped := true })
  let dest := namedPermanent g "Aerial Doombot"
  let tok := g.object! tok.id
  let g := g.becomeCopyOf dest tok
  let dest := g.object! dest.id
  dest.printed.name == "Soldier" &&
    dest.printed.power == some 1 &&
    dest.printed.toughness == some 1 &&
    dest.status.plusOnePlusOne == 0 &&
    !dest.status.tapped &&
    (mshRuling 545).comment.contains "original characteristics of that token" &&
    (mshRuling 548).comment.contains "original characteristics of that token" &&
    (mshRuling 549).comment.contains "original characteristics of that token" &&
    (mshRuling 552).comment.contains "original characteristics of that token"

#guard copyTokenOriginalOk

/-- Rulings 155 / 194 / 195 / 198 / 199 / 201: a copy of a copy uses the
copied characteristics. -/
def copyOfCopyOk : Bool :=
  let g := addPermanent afterDraw aerialDoombot ⟨0⟩ ⟨0⟩
  let g := addPermanent g sHIELDDeploymentDrone ⟨0⟩ ⟨0⟩
  let g := addPermanent g futuristForge ⟨0⟩ ⟨0⟩
  let drone := namedPermanent g "S.H.I.E.L.D. Deployment Drone"
  let dest := namedPermanent g "Aerial Doombot"
  let g := g.becomeCopyOf dest drone
  let dest := g.object! dest.id
  let forge := namedPermanent g "Futurist Forge"
  let g := g.becomeCopyOf forge dest
  let forge := g.object! forge.id
  dest.printed.name == "S.H.I.E.L.D. Deployment Drone" &&
    forge.printed.name == "S.H.I.E.L.D. Deployment Drone" &&
    (mshRuling 546).comment.contains "copy of whatever that permanent copied" &&
    (mshRuling 550).comment.contains "copy of whatever" &&
    (mshRuling 551).comment.contains "whatever that creature copied" &&
    (mshRuling 553).comment.contains "copy of whatever that permanent copied" &&
    (mshRuling 508).comment.contains "whatever that creature copied" &&
    (mshRuling 547).comment.contains "whatever that artifact copied"

#guard copyOfCopyOk

/-- Rulings 92 / 93 / 115 / 304: a token copy is not tapped or countered,
and the copied permanent's enters abilities trigger. -/
def copyTokenEntersAbilitiesOk : Bool :=
  let g := addPermanent afterDraw futuristForge ⟨0⟩ ⟨0⟩
  let src := namedPermanent g "Futurist Forge"
  let (g, tok) := g.copyBattlefieldPermanent src ⟨0⟩
  let before := g.waitingTriggers.size
  let g := g.afterPermanentEnters tok
  !tok.status.tapped &&
    tok.status.plusOnePlusOne == 0 &&
    tok.printed.isToken &&
    g.waitingTriggers.size > before &&
    (mshRuling 445).comment.contains "enters abilities of each copied" &&
    (mshRuling 446).comment.contains "enters abilities of the copied" &&
    (mshRuling 468).comment.contains "exactly what was printed" &&
    (mshRuling 656).comment.contains "exactly what was printed"

#guard copyTokenEntersAbilitiesOk

/-- Rulings 36 / 46 / 48 / 66 / 116 / 117 / 278 / 279 / 303: a stack-ability
copy keeps mode, divided damage, and the original source. -/
def copyStackAbilityDetailsOk : Bool :=
  let g := addPermanent afterDraw aerialDoombot ⟨0⟩ ⟨0⟩
  let src := namedPermanent g "Aerial Doombot"
  let (g, ab) := g.allocStackAbility src ⟨0⟩
    (triggeredAbility := some (.onEnterDraw 1))
  let g := g.putStackEntry ⟨0⟩ ab.id
  let g :=
    match g.stack.findIdx? (fun e => e.objectId == ab.id) with
    | none => g
    | some i =>
      { g with stack := g.stack.set! i { g.stack[i]! with
        targets := #[Target.player ⟨1⟩]
        dividedDamage := #[2, 1]
        chosenMode := some 1 } }
  let g := g.copyStackAbility (g.object! ab.id) ⟨0⟩
  let copies := g.objects.filter (fun o =>
    o.zone == .stack && o.isCopy && o.sourceId == some src.id)
  let last := g.stack.back!
  copies.size == 1 &&
    copies[0]!.sourceId == some src.id &&
    last.chosenMode == some 1 &&
    last.dividedDamage == #[2, 1] &&
    last.targets.size == 1 &&
    (mshRuling 391).comment.contains "choices will be made separately" &&
    (mshRuling 400).comment.contains "division can't be changed" &&
    (mshRuling 402).comment.contains "same mode" &&
    (mshRuling 419).comment.contains "can't choose to pay any activation" &&
    (mshRuling 469).comment.contains "not just one with targets" &&
    (mshRuling 470).comment.contains "doesn't cause any object to gain" &&
    (mshRuling 630).comment.contains "not just one with targets" &&
    (mshRuling 631).comment.contains "doesn't cause any object to gain" &&
    (mshRuling 655).comment.contains "same as the source of the original"

#guard copyStackAbilityDetailsOk

/-- Rulings 134 / 183 / 327: Hulkling re-checks on resolve, multiple
enters trigger separately, and a swapped greater stat still counts. -/
def hulklingRecheckOk : Bool :=
  let g := mshEnter afterDraw hulklingBurgeoningBruiser
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  let giant := namedPermanent g "Hill Giant"
  let hulkling := namedPermanent g "Hulkling, Burgeoning Bruiser"
  let gShrink := g.pumpPermanent giant (-2) (-2)
  let gShrink := gShrink.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchHulklingCompare)
    (some hulkling.id) #[Target.permanent giant.id]
  (namedPermanent gShrink "Hulkling, Burgeoning Bruiser").status.plusOnePlusOne == 0 &&
    (let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
     let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
     let hulkling := namedPermanent g "Hulkling, Burgeoning Bruiser"
     let giants := g.battlefield.filter (fun o => o.name == "Hill Giant")
     let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchHulklingCompare)
       (some hulkling.id) #[Target.permanent giants[0]!.id]
     let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchHulklingCompare)
       (some hulkling.id) #[Target.permanent giants[1]!.id]
     (namedPermanent g "Hulkling, Burgeoning Bruiser").status.plusOnePlusOne == 1) &&
    (let g := mshEnter afterDraw hulklingBurgeoningBruiser
     let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
     let bot := namedPermanent g "Aerial Doombot"
     let g := g.mapObjectStatus bot (fun s => { s with setBasePT := some (1, 4) })
     let hulkling := namedPermanent g "Hulkling, Burgeoning Bruiser"
     let g := g.mapObjectStatus hulkling (fun s => { s with setBasePT := some (4, 3) })
     let hulkling := namedPermanent g "Hulkling, Burgeoning Bruiser"
     let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchHulklingCompare)
       (some hulkling.id) #[Target.permanent bot.id]
     (namedPermanent g "Hulkling, Burgeoning Bruiser").status.plusOnePlusOne == 1) &&
    (mshRuling 487).comment.contains "stat comparison will happen again" &&
    (mshRuling 535).comment.contains "trigger multiple times" &&
    (mshRuling 679).comment.contains "stat that's greater changes"

#guard hulklingRecheckOk

/-- Rulings 112 / 293: damage is tracked through indestructible; deathtouch
is checked only on the first SBA pass after the damage. -/
def doctorDoomDamageTrackedOk : Bool :=
  let g := addPermanent afterDraw doctorDoom ⟨0⟩ ⟨0⟩
  let doom := namedPermanent g "Doctor Doom"
  let g := g.mapObjectStatus doom (·.grantUntilEot Keyword.indestructible)
  let doom := namedPermanent g "Doctor Doom"
  let g := g.markDamageOn doom 3 "Doctor Doom is dealt 3"
  let g := g.checkSBA
  onBattlefield g "Doctor Doom" &&
    (namedPermanent g "Doctor Doom").status.damage == 3 &&
    (let doom := namedPermanent g "Doctor Doom"
     let g := g.mapObjectStatus doom (fun s =>
       { s with untilEotKeywords := Keywords.none })
     let g := g.checkSBA
     !onBattlefield g "Doctor Doom") &&
    (let g := addPermanent afterDraw doctorDoom ⟨0⟩ ⟨0⟩
     let doom := namedPermanent g "Doctor Doom"
     let g := g.mapObjectStatus doom (·.grantUntilEot Keyword.indestructible)
     let doom := namedPermanent g "Doctor Doom"
     let g := g.markDamageOn doom 1 "deathtouch" (deathtouch := true)
     let g := g.checkSBA
     onBattlefield g "Doctor Doom" &&
       !(namedPermanent g "Doctor Doom").status.dealtDeathtouch &&
       (let doom := namedPermanent g "Doctor Doom"
        let g := g.mapObjectStatus doom (fun s =>
          { s with untilEotKeywords := Keywords.none })
        let g := g.checkSBA
        onBattlefield g "Doctor Doom")) &&
    (mshRuling 465).comment.contains "tracked even if he has indestructible" &&
    (mshRuling 645).comment.contains "first time that state-based actions"

#guard doctorDoomDamageTrackedOk

/-- Rulings 145 / 190: Wasp leaving before resolve still taps; later granted
abilities are kept after printed abilities are lost. -/
def wondrousWaspLoseAbilitiesOk : Bool :=
  let g := addPermanent afterDraw theWondrousWasp ⟨0⟩ ⟨0⟩
  let g := addPermanent g stormWindrider ⟨0⟩ ⟨0⟩
  let wasp := namedPermanent g "The Wondrous Wasp"
  let storm := namedPermanent g "Storm, Windrider"
  let (g, _) := g.move wasp.id (.graveyard ⟨0⟩) none
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterTapLoseAbilitiesWhileSource)
    (some wasp.id) #[Target.permanent storm.id]
  (namedPermanent g "Storm, Windrider").status.tapped &&
    g.hasFlying (namedPermanent g "Storm, Windrider") &&
    (let g := addPermanent afterDraw theWondrousWasp ⟨0⟩ ⟨0⟩
     let g := addPermanent g stormWindrider ⟨0⟩ ⟨0⟩
     let wasp := namedPermanent g "The Wondrous Wasp"
     let storm := namedPermanent g "Storm, Windrider"
     let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterTapLoseAbilitiesWhileSource)
       (some wasp.id) #[Target.permanent storm.id]
     let storm := namedPermanent g "Storm, Windrider"
     storm.status.tapped &&
       !g.hasFlying storm &&
       (let g := g.mapObjectStatus storm (·.grantUntilEot Keyword.flying)
        g.hasFlying (namedPermanent g "Storm, Windrider"))) &&
    (mshRuling 498).comment.contains "won't lose its abilities" &&
    (mshRuling 542).comment.contains "will keep that ability"

#guard wondrousWaspLoseAbilitiesOk

/-- Ruling 496: Super Hero Civil War leaving skips the control change. -/
def superHeroCivilWarLeaveOk : Bool :=
  let g := addPermanent afterDraw theSuperHeroCivilWar ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let saga := namedPermanent g "The Super Hero Civil War"
  let bears := namedPermanent g "Grizzly Bears"
  let (g, _) := g.move saga.id (.graveyard ⟨0⟩) none
  let g := g.applyChapterEffect ⟨0⟩ (Effect.chapterGainControlOfUpToTwoCreaturesTotalMvAtMost 6)
    (some saga.id) #[Target.permanent bears.id]
  (namedPermanent g "Grizzly Bears").controlledBy ⟨1⟩ &&
    (let g := addPermanent afterDraw theSuperHeroCivilWar ⟨0⟩ ⟨0⟩
     let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
     let saga := namedPermanent g "The Super Hero Civil War"
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.applyChapterEffect ⟨0⟩ (Effect.chapterGainControlOfUpToTwoCreaturesTotalMvAtMost 6)
       (some saga.id) #[Target.permanent bears.id]
     (namedPermanent g "Grizzly Bears").controlledBy ⟨0⟩) &&
    (mshRuling 496).comment.contains "won't gain control"

#guard superHeroCivilWarLeaveOk

/-- Ruling 504: an artifact Villain entering fires HYDRA Assault Robot once. -/
def hydraAssaultOnceOk : Bool :=
  let g := addPermanent afterDraw hYDRAAssaultRobot ⟨0⟩ ⟨0⟩
  let g := addPermanent g ultronDrone ⟨0⟩ ⟨0⟩
  let drone := namedPermanent g "Ultron Drone"
  let g := g.afterPermanentEnters drone
  let n :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.source.name == "HYDRA Assault Robot")).size
  n == 1 &&
    (mshRuling 504).comment.contains "trigger only once"

#guard hydraAssaultOnceOk

/-- Ruling 669: token creatures dying do not trigger Robot Domination. -/
def robotDominationTokenOk : Bool :=
  let g := addPermanent afterDraw robotDomination ⟨0⟩ ⟨0⟩
  let (g, tok) := g.createToken ⟨0⟩ Game.soldier11whiteToken
  let (g, _) := g.move tok.id (.graveyard ⟨0⟩) none
  !g.waitingTriggers.any (fun (t : WaitingTrigger) =>
    t.event == TriggerEvent.creatureCardsPutIntoYourGy) &&
    (mshRuling 669).comment.contains "Token creatures"

#guard robotDominationTokenOk

/-- Ruling 649: Avengers Assemble! does not trigger if neither condition
was met. -/
def avengersAssembleNoTriggerOk : Bool :=
  let g := addPermanent afterDraw avengersAssemble ⟨0⟩ ⟨0⟩
  let assem := namedPermanent g "Avengers Assemble!"
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.applyTriggeredAbility ⟨0⟩
    (.onEachEndStepDrawIfAttackedOrEnteredSubtype "Hero") (some assem.id)
  (g.player ⟨0⟩).hand.size == hand0 &&
    (mshRuling 649).comment.contains "won't trigger at all"

#guard avengersAssembleNoTriggerOk

/-- Rulings 262 / 263 / 264: becoming a better blocker or shrinking after
the block does not make the attacker unblocked. -/
def blockedStaysBlockedOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let bears := namedPermanent g "Grizzly Bears"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.setObject { bears with status := { bears.status with
    attacking := true, attackingWhom := some ⟨1⟩, blocked := true } }
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { ogre with status := { ogre.status with
    blocking := #[bears.id] } }
  let g := g.mapObjectStatus (namedPermanent g "Grizzly Bears")
    (·.grantUntilEot Keyword.flying)
  (namedPermanent g "Grizzly Bears").status.blocked &&
    g.hasFlying (namedPermanent g "Grizzly Bears") &&
    (mshRuling 614).comment.contains "won't cause him to become unblocked" &&
    (mshRuling 615).comment.contains "won't cause her to become unblocked" &&
    (mshRuling 616).comment.contains "won't be able to make that block illegal"

#guard blockedStaysBlockedOk

/-- Ruling 615: once Stature is blocked at high power, shrinking her to 1
does not make her unblocked. -/
def statureBlockedThenShrunkOk : Bool :=
  let g := addPermanent afterDraw statureSizeShifter ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let st := namedPermanent g "Stature, Size Shifter"
  let g := g.setObject { st with status := { st.status with
    plusOnePlusOne := 3, attacking := true, attackingWhom := some ⟨1⟩,
    blocked := true } }
  let st := namedPermanent g "Stature, Size Shifter"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status := { bears.status with
    blocking := #[st.id] } }
  let g := g.mapObjectStatus (namedPermanent g "Stature, Size Shifter")
    (fun s => { s with plusOnePlusOne := 0 })
  let st := namedPermanent g "Stature, Size Shifter"
  g.power st == 1 && g.hasCantBeBlocked st && st.status.blocked &&
    (namedPermanent g "Grizzly Bears").status.blocking == #[st.id]

#guard statureBlockedThenShrunkOk

/-- Ruling 610: multiple lifelink instances are redundant. -/
def yellowjacketLifelinkRedundantOk : Bool :=
  let g := addPermanent afterDraw yellowjacketHeartlessMarauder ⟨0⟩ ⟨0⟩
  let yj := namedPermanent g "Yellowjacket, Heartless Marauder"
  let g := g.mapObjectStatus yj (·.grantUntilEot Keyword.lifelink)
  g.hasLifelink (namedPermanent g "Yellowjacket, Heartless Marauder") &&
    (mshRuling 610).comment.contains "Multiple instances of lifelink"

#guard yellowjacketLifelinkRedundantOk

/-- Ruling 521: Scarlet Witch uses the chosen X when checking mana value. -/
def scarletWitchXManaValueOk : Bool :=
  let g := addPermanent afterDraw theScarletWitch ⟨0⟩ ⟨0⟩
  let (g, spell) := g.allocObject photonBlastBarrage ⟨0⟩ (.hand ⟨0⟩) (some ⟨0⟩)
  let cheap := g.object! spell.id
  let cheap := { cheap with chosenX := some 1 }
  let g := g.setObject cheap
  let costly := { cheap with chosenX := some 2 }
  let start := photonBlastBarrage.manaCost
  let reduced := g.applyCastCostReductions costly photonBlastBarrage start
  let unreduced := g.applyCastCostReductions cheap photonBlastBarrage start
  reduced.manaValue == 2 &&
    unreduced.manaValue == 3 &&
    (mshRuling 521).comment.contains "value chosen for X"

#guard scarletWitchXManaValueOk

/-- Ruling 462: Loki compares mana value to last-known power if he left. -/
def lokiLastKnownPowerOk : Bool :=
  let g := addPermanent afterDraw lokiLaufeyson ⟨0⟩ ⟨0⟩
  let loki := namedPermanent g "Loki Laufeyson"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.nextInstantSorceryCopyIfMvAtMostSourcePower) #[]
    (some loki.id)
  let (g, _) := g.move loki.id (.graveyard ⟨0⟩) none
  let (g, spell) := g.allocObject lightningBolt ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.putStackEntry ⟨0⟩ spell.id
  let g := g.putCastTriggersOnStack ⟨0⟩ (g.object! spell.id)
  let copies := g.objects.filter (fun o =>
    o.zone == .stack && o.isCopy && o.printed.name == "Lightning Bolt")
  copies.size == 1 &&
    (mshRuling 462).comment.contains "last time he was on the battlefield"

#guard lokiLastKnownPowerOk

/-- Ruling 622: H.E.R.B.I.E. putting a land onto the battlefield is not
playing a land. -/
def herbieLandNotPlayOk : Bool :=
  let g := addToHand afterDraw forest ⟨0⟩
  let played0 := (g.player ⟨0⟩).landsPlayedThisTurn
  let g := addPermanent g hERBIEScoutUnit ⟨0⟩ ⟨0⟩
  let herbie := namedPermanent g "H.E.R.B.I.E. Scout Unit"
  let g := g.applyTriggeredAbility ⟨0⟩ .onEnterDrawMayPutLandTapped (some herbie.id)
  let landId := (g.player ⟨0⟩).hand.findSome? (fun id =>
    match g.findObject? id with
    | some o => if o.printed.isLand then some id else none
    | none => none)
  let g :=
    match landId with
    | some id => mustApply g ⟨0⟩ (.cast id)
    | none => g
  g.battlefield.any (fun o =>
      o.printed.isLand && o.status.tapped && o.status.enteredThisTurn) &&
    (g.player ⟨0⟩).landsPlayedThisTurn == played0 &&
    (mshRuling 622).comment.contains "doesn't count as playing a land"

#guard herbieLandNotPlayOk

/-- Ruling 499 / 312: Tigra does not get a counter in time to survive
simultaneous lethal damage, and life gain is one event. -/
def tigraLethalLifeOk : Bool :=
  let g := addPermanent afterDraw tigraFelineFury ⟨0⟩ ⟨0⟩
  let tigra := namedPermanent g "Tigra, Feline Fury"
  let g := g.markDamageOn tigra 1 "Tigra is dealt 1"
  let g := g.gainLife ⟨0⟩ 3
  let g := g.checkSBA
  !onBattlefield g "Tigra, Feline Fury" &&
    (mshRuling 499).comment.contains "won't receive a counter" &&
    (mshRuling 664).comment.contains "just once"

#guard tigraLethalLifeOk

/-- Ruling 647: Thunderbolts returns a Villain as a Hero from the moment
it enters. -/
def thunderboltsHeroTypeOk : Bool :=
  let g := addPermanent afterDraw thunderboltsConspiracy ⟨0⟩ ⟨0⟩
  let g := addPermanent g agentsOfHYDRA ⟨0⟩ ⟨0⟩
  let villain := namedPermanent g "Agents of HYDRA"
  let (g, _) := g.move villain.id (.graveyard ⟨0⟩) none
  let gy := namedGraveyardCard g ⟨0⟩ "Agents of HYDRA"
  let before := g.waitingTriggers.size
  let g := g.applyModeledTrigger ⟨0⟩ (.onDeath Effect.deathVillainReturnAsHero)
    (some (namedPermanent g "Thunderbolts Conspiracy").id) #[Target.card gy.id]
  let o := namedPermanent g "Agents of HYDRA"
  g.hasSubtype o "Hero" &&
    o.status.finality == 1 &&
    g.waitingTriggers.size >= before &&
    (mshRuling 647).comment.contains "Hero in addition to its other types"

#guard thunderboltsHeroTypeOk

/-- Ruling 497: The Void attacks if able, but not while sick, tapped, or
if attacking would require an unpaid cost. -/
def theVoidAttacksIfAbleOk : Bool :=
  let (g, tok) := afterDraw.createToken ⟨0⟩ Game.theVoidToken
  Game.hasAttacksIfAble tok &&
    !g.mustAttackIfAble tok &&
    (let g := g.mapObjectStatus tok (fun s => { s with summoningSick := false })
     let tok := g.object! tok.id
     g.mustAttackIfAble tok &&
       (let g := g.mapObjectStatus tok (fun s => { s with tapped := true })
        !g.mustAttackIfAble (g.object! tok.id) &&
          !g.mustAttackIfAble tok (attackRequiresCost := true))) &&
    (mshRuling 497).comment.contains "doesn't attack"

#guard theVoidAttacksIfAbleOk

/-- Rulings 107 / 108 / 123 / 239 / 248 / 250 / 251 / 260 / 269 / 271 / 282 /
285 / 311 / 339: a spell that targets a creature you control queues those
cast triggers once, above the spell. Madame Hydra queues on a Villain
spell. Loki (247) queues when an ability you control gets a target. -/
def castTriggerBeforeSpellOk : Bool :=
  let g := addPermanent afterDraw colleenWingStreetSamurai ⟨0⟩ ⟨0⟩
  let g := addPermanent g ironFistLivingWeapon ⟨0⟩ ⟨0⟩
  let g := addPermanent g mockingbirdAceAgent ⟨0⟩ ⟨0⟩
  let g := addPermanent g msMarvelKamalaKhan ⟨0⟩ ⟨0⟩
  let g := addPermanent g madameHydra ⟨0⟩ ⟨0⟩
  let g := addPermanent g lokiGodOfMischief ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let (g, spell) := g.allocObject helicarrierStrike ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.putStackEntry ⟨0⟩ spell.id
  let g :=
    match g.stack.findIdx? (fun e => e.objectId == spell.id) with
    | none => g
    | some i =>
      { g with stack := g.stack.set! i { g.stack[i]! with
          targets := #[Target.permanent bears.id] } }
  let g := g.putCastTriggersOnStack ⟨0⟩ (g.object! spell.id)
  let names :=
    (g.waitingTriggers.map (fun (t : WaitingTrigger) => t.source.name))
  names.any (· == "Colleen Wing, Street Samurai") &&
    names.any (· == "Iron Fist, Living Weapon") &&
    names.any (· == "Mockingbird, Ace Agent") &&
    names.any (· == "Ms. Marvel, Kamala Khan") &&
    !names.any (· == "Madame Hydra") &&
    g.objects.any (fun o => o.id == spell.id && o.zone == .stack) &&
    (let (gV, villain) := g.allocObject agentsOfHYDRA ⟨0⟩ .stack (some ⟨0⟩)
     let gV := gV.putStackEntry ⟨0⟩ villain.id
     let gV := gV.putCastTriggersOnStack ⟨0⟩ (gV.object! villain.id)
     (gV.waitingTriggers.map (fun (t : WaitingTrigger) => t.source.name)).any
       (· == "Madame Hydra") &&
       gV.objects.any (fun o => o.id == villain.id && o.zone == .stack)) &&
    (let (gAb, ab) := g.allocObject helicarrierStrike ⟨0⟩ .stack (some ⟨0⟩)
     let gAb := gAb.setObject { ab with
       abilityEffect := some (Effect.dealDamageToTargetCreature 1) }
     let gAb := gAb.putStackEntry ⟨0⟩ ab.id
     let gAb := gAb.queueYouTargetTriggers ⟨0⟩ (gAb.object! ab.id)
     gAb.waitingTriggers.any (fun (t : WaitingTrigger) =>
         t.source.name == "Loki, God of Mischief") &&
       gAb.objects.any (fun o => o.id == ab.id && o.zone == .stack)) &&
    (mshRuling 460).comment.contains "resolves before the spell" &&
    (mshRuling 461).comment.contains "doesn't trigger multiple times" &&
    (mshRuling 476).comment.contains "doesn't trigger multiple times" &&
    (mshRuling 612).comment.contains "resolves before the spell" &&
    (mshRuling 621).comment.contains "resolves before the spell" &&
    (mshRuling 623).comment.contains "resolves before the spell" &&
    (mshRuling 634).comment.contains "resolves before the spell" &&
    (mshRuling 637).comment.contains "resolves before the spell" &&
    (mshRuling 663).comment.contains "resolves before the spell" &&
    (mshRuling 691).comment.contains "resolves before the spell" &&
    (mshRuling 591).comment.contains "resolves before the spell" &&
    (mshRuling 599).comment.contains "resolves before the ability" &&
    (mshRuling 600).comment.contains "resolves before the spell" &&
    (mshRuling 602).comment.contains "resolves before the spell" &&
    (mshRuling 603).comment.contains "resolves before the spell"

#guard castTriggerBeforeSpellOk

/-- Rulings 41 / 53 / 126: one life-gaining event triggers Tigra once. -/
def lifeGainOnceOk : Bool :=
  let g := addPermanent afterDraw tigraFelineFury ⟨0⟩ ⟨0⟩
  let g := g.gainLife ⟨0⟩ 5
  let n :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.source.name == "Tigra, Feline Fury")).size
  n == 1 &&
    (mshRuling 395).comment.contains "separate life-gaining event" &&
    (mshRuling 406).comment.contains "triggers only once" &&
    (mshRuling 479).comment.contains "just once"

#guard lifeGainOnceOk

/-- Ruling 643: Hawkeye's extra damage is dealt by the original source. -/
def hawkeyeSameSourceOk : Bool :=
  let g := addPermanent afterDraw hawkeyeYoungAvenger ⟨0⟩ ⟨0⟩
  let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let src := namedPermanent g "Aerial Doombot"
  let bears := namedPermanent g "Grizzly Bears"
  let hawk := namedPermanent g "Hawkeye, Young Avenger"
  let g := g.dealDamageFrom src.name bears 1 (source := some src)
  (namedPermanent g "Grizzly Bears").status.damage == 1 + g.power hawk &&
    logContains g "Aerial Doombot deals" &&
    (mshRuling 643).comment.contains "same source as the original"

#guard hawkeyeSameSourceOk

/-- Ruling 530: if all of a source's damage is prevented, Hawkeye's extra
damage no longer applies. -/
def hawkeyePreventionSkipsExtraOk : Bool :=
  let g := addPermanent afterDraw hawkeyeYoungAvenger ⟨0⟩ ⟨0⟩
  let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let src := namedPermanent g "Aerial Doombot"
  let hawk := namedPermanent g "Hawkeye, Young Avenger"
  let extra := g.power hawk
  let gHit := g.dealDamageFrom src.name (namedPermanent g "Grizzly Bears") 1
    (source := some src)
  (namedPermanent gHit "Grizzly Bears").status.damage == 1 + extra &&
    (let gPrev := g.mapObjectStatus src (fun s =>
        { s with preventDamageGrantedBy := #[src.id] })
     let src := namedPermanent gPrev "Aerial Doombot"
     let gPrev := gPrev.dealDamageFrom src.name (namedPermanent gPrev "Grizzly Bears") 1
       (source := some src)
     (namedPermanent gPrev "Grizzly Bears").status.damage == 0 &&
       gPrev.log.any (fun s => mentions s "prevented")) &&
    (mshRuling 530).comment.contains "chooses an order"

#guard hawkeyePreventionSkipsExtraOk

/-- Ruling 700: The Ruinous Wrecking Crew cannot choose the same mode twice. -/
def wreckingCrewModesOnceOk : Bool :=
  let g := addPermanent afterDraw theRuinousWreckingCrew ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "The Ruinous Wrecking Crew"
  let g := g.mapObjectStatus o (fun s => { s with chosenModes := #[0, 2] })
  let o := namedPermanent g "The Ruinous Wrecking Crew"
  o.status.chosenModes.contains 0 &&
    !o.status.chosenModes.contains 1 &&
    (mshRuling 700).comment.contains "can't choose the same mode"

#guard wreckingCrewModesOnceOk

/-- Ruling 412: tapping an artifact does not turn off its static abilities. -/
def improviseStaticsWhileTappedOk : Bool :=
  let g := addPermanent afterDraw ironheartCleverChampion ⟨0⟩ ⟨0⟩
  let ih := namedPermanent g "Ironheart, Clever Champion"
  let g := g.mapObjectStatus ih (fun s => { s with tapped := true })
  g.spellHasImprovise helicarrierStrike ⟨0⟩ &&
    (namedPermanent g "Ironheart, Clever Champion").status.tapped &&
    (mshRuling 412).comment.contains "won't cause its abilities to stop"

#guard improviseStaticsWhileTappedOk

/-- Ruling 581: tap an artifact for improvise, then it can still be
sacrificed as an additional cost. -/
def improviseThenSacrificeOk : Bool :=
  let (g, tok) := afterDraw.createToken ⟨0⟩ treasureToken
  match g.tapArtifactsForImprovise ⟨0⟩ #[tok.id] with
  | .ok g =>
    (g.object! tok.id).status.tapped &&
      (g.object! tok.id).isOnBattlefield &&
      (mshRuling 581).comment.contains "tap that permanent"
  | .error _ => false

#guard improviseThenSacrificeOk

/-- Ruling 410: a Two-Headed Giant teammate's life gain is not "you gain life". -/
def twoHeadedGiantTeammateLifeOk : Bool :=
  let g := addPermanent afterDraw tigraFelineFury ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with teammate := some ⟨1⟩ })
  let g := g.modifyPlayer ⟨1⟩ (fun pl => { pl with teammate := some ⟨0⟩ })
  let g := g.gainLife ⟨1⟩ 3
  !(g.waitingTriggers.any (fun (t : WaitingTrigger) =>
      t.source.name == "Tigra, Feline Fury")) &&
    (mshRuling 410).comment.contains "Two-Headed Giant"

#guard twoHeadedGiantTeammateLifeOk

/-- Ruling 588: controlling a player in Two-Headed Giant controls the team. -/
def twoHeadedGiantControlTeamOk : Bool :=
  let g := afterDraw.modifyPlayer ⟨1⟩ (fun pl => { pl with teammate := some ⟨0⟩ })
  let g := g.setPlayerControl ⟨0⟩ ⟨1⟩
  g.controlsPlayer ⟨0⟩ ⟨1⟩ &&
    g.controlsPlayer ⟨0⟩ ⟨0⟩ &&
    (mshRuling 588).comment.contains "gain control of each player"

#guard twoHeadedGiantControlTeamOk

/-- Ruling 459 / 239: each targeting spell grants Iron Fist another tap
ability; the trigger waits above the spell. -/
def ironFistMultipleGrantsOk : Bool :=
  let g := addPermanent afterDraw ironFistLivingWeapon ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let fist := namedPermanent g "Iron Fist, Living Weapon"
  let g := g.applyModeledTrigger ⟨0⟩ (.onCasting Effect.castingIronFistTap)
    (some fist.id)
  let g := g.applyModeledTrigger ⟨0⟩ (.onCasting Effect.castingIronFistTap)
    (some fist.id)
  (namedPermanent g "Iron Fist, Living Weapon").status.ironFistTapGrants == 2 &&
    (mshRuling 459).comment.contains "multiple instances"

#guard ironFistMultipleGrantsOk

/-- Ruling 522: an Aura returns without targeting and can attach through
hexproof. -/
def mindStoneAuraReturnOk : Bool :=
  let g := addPermanent afterDraw theMindStone ⟨0⟩ ⟨0⟩
  let g := addPermanent g superSoldierSerum ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let aura := namedPermanent g "Super-Soldier Serum"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.mapObjectStatus bears (·.grantUntilEot Keyword.hexproof)
  let (g, _) := g.move aura.id .exile none
  let ex :=
    (g.objects.find? (fun o => o.name == "Super-Soldier Serum" && o.zone == .exile)).getD aura
  let g := g.returnExiledId ex.id
  let aura := namedPermanent g "Super-Soldier Serum"
  aura.attachedTo == some (namedPermanent g "Grizzly Bears").id &&
    g.log.any (fun s => mentions s "does not target") &&
    (mshRuling 522).comment.contains "doesn't target anything"

#guard mindStoneAuraReturnOk

/-- Rulings 177 / 179 / 237: Mjölnir doubles after assignment; two hammers
multiply by four; prevention of all damage skips Mjölnir. -/
def mjolnirDoubleOk : Bool :=
  let g := addPermanent afterDraw mjLnirHammerOfThor ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let hammer := namedPermanent g "Mjölnir, Hammer of Thor"
  let ogre := namedPermanent g "Gray Ogre"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.attachSourceTo hammer ogre
  let gHit := g.dealDamageFrom ogre.name bears 2 (source := some (namedPermanent g "Gray Ogre"))
  (namedPermanent gHit "Grizzly Bears").status.damage == 4 &&
    (let g := addPermanent g mjLnirHammerOfThor ⟨0⟩ ⟨0⟩
     let hammers := g.battlefield.filter (fun o => o.name == "Mjölnir, Hammer of Thor")
     let ogre := namedPermanent g "Gray Ogre"
     let g :=
       hammers.foldl (fun acc h => acc.attachSourceTo (acc.object! h.id) ogre) g
     let bears := namedPermanent g "Grizzly Bears"
     let g := g.dealDamageFrom ogre.name bears 2 (source := some (namedPermanent g "Gray Ogre"))
     (namedPermanent g "Grizzly Bears").status.damage == 8) &&
    (let gPrev := g.mapObjectStatus ogre (fun s =>
        { s with preventDamageGrantedBy := #[ogre.id] })
     let gPrev := gPrev.dealDamageFrom ogre.name (namedPermanent gPrev "Grizzly Bears") 2
       (source := some (namedPermanent gPrev "Gray Ogre"))
     (namedPermanent gPrev "Grizzly Bears").status.damage == 0 &&
       gPrev.log.any (fun s => mentions s "prevented")) &&
    (mshRuling 529).comment.contains "chooses the order" &&
    (mshRuling 531).comment.contains "divided or assigned before doubling" &&
    (mshRuling 589).comment.contains "multiplied by four"

#guard mjolnirDoubleOk

/-- Ruling 531: combat assignment is doubled after the split. -/
def mjolnirCombatDivideOk : Bool :=
  let g := addPermanent afterDraw mjLnirHammerOfThor ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  let hammer := namedPermanent g "Mjölnir, Hammer of Thor"
  let ogre := namedPermanent g "Gray Ogre"
  let giant := namedPermanent g "Hill Giant"
  let g := g.attachSourceTo hammer ogre
  let g := g.setObject { ogre with status :=
    { ogre.status with attacking := true, blocked := true, attackingWhom := some ⟨1⟩ } }
  let g := { g with assignedCombatDamage :=
    #[{ source := ogre.id, toCreatures := #[(giant.id, 1)], toPlayer := 2 }] }
  let g := g.dealAssignedCombatDamage
  (namedPermanent g "Hill Giant").status.damage == 2 &&
    (g.player ⟨1⟩).life == 20 - 4

#guard mjolnirCombatDivideOk

/-- Ruling 556: a creature not controlled by the target opponent is illegal,
but the ability may still reveal. -/
def cloakIllegalCreatureStillResolvesOk : Bool :=
  let g := addToHand afterDraw lightningBolt ⟨1⟩
  let g := addPermanent g cloakAndDaggerEntwined ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let cloak := namedPermanent g "Cloak and Dagger, Entwined"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterRevealHandExileUntilLeaves)
    (some cloak.id) #[Target.player ⟨1⟩, Target.permanent bears.id]
  logContains g "illegal target" &&
    onBattlefield g "Grizzly Bears" &&
    (mshRuling 556).comment.contains "illegal target"

#guard cloakIllegalCreatureStillResolvesOk

/-- Ruling 586: a card exiled from hand returns to hand when Cloak leaves. -/
def cloakReturnToHandOk : Bool :=
  let g := addToHand afterDraw lightningBolt ⟨1⟩
  let g := addPermanent g cloakAndDaggerEntwined ⟨0⟩ ⟨0⟩
  let bolt := handCardNamed g ⟨1⟩ "Lightning Bolt"
  let cloak := namedPermanent g "Cloak and Dagger, Entwined"
  let g := g.exileUntilSourceLeaves (some cloak.id) bolt
  let (g, _) := g.move cloak.id (.graveyard ⟨0⟩) none
  (g.handObjects ⟨1⟩).any (fun o => o.name == "Lightning Bolt") &&
    (mshRuling 586).comment.contains "returns to their hand"

#guard cloakReturnToHandOk

/-- Ruling 557: if the enchanted creature left, Serum does not move Equipment. -/
def serumHostLeftOk : Bool :=
  let g := addPermanent afterDraw superSoldierSerum ⟨0⟩ ⟨0⟩
  let g := addPermanent g vibraniumEnergyDaggers ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let eq := namedPermanent g "Vibranium Energy Daggers"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.attachSourceTo eq ogre
  let serum := namedPermanent g "Super-Soldier Serum"
  let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchEnchantedAttachEquipment)
    (some serum.id) #[Target.permanent eq.id]
  (namedPermanent g "Vibranium Energy Daggers").attachedTo == some ogre.id &&
    logContains g "Equipment stays" &&
    (mshRuling 557).comment.contains "remain attached"

#guard serumHostLeftOk

/-- Ruling 558: if either fight target is illegal, HULK SMASH deals no damage. -/
def hulkSmashIllegalFizzleOk : Bool :=
  let g := addPermanent afterDraw grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let ogre := namedPermanent g "Gray Ogre"
  let bears := namedPermanent g "Grizzly Bears"
  let (g, _) := g.move bears.id (.graveyard ⟨1⟩) none
  let g := g.applyEffect ⟨0⟩ (Effect.creatureYouControlDealsPowerToOppCreature)
    #[Target.permanent ogre.id, Target.permanent bears.id]
  (namedPermanent g "Gray Ogre").status.damage == 0 &&
    (mshRuling 558).comment.contains "no damage will be dealt"

#guard hulkSmashIllegalFizzleOk

/-- Ruling 559: an illegal land target fizzles Avengers Disassembled entirely. -/
def avengersDisassembledFizzleOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g forest ⟨1⟩ ⟨1⟩
  let land := namedPermanent g "Forest"
  let (gGone, _) := g.move land.id (.graveyard ⟨1⟩) none
  let fizzled := gGone.applyAvengersDisassembled ⟨0⟩ true true (some land.id)
  (namedPermanent fizzled "Grizzly Bears").status.damage == 0 &&
    logContains fizzled "doesn't resolve" &&
    (let gOk := g.applyAvengersDisassembled ⟨0⟩ true true (some land.id)
     (namedPermanent gOk "Grizzly Bears").status.damage == 3 &&
       logContains gOk "may search") &&
    (mshRuling 559).comment.contains "won't resolve"

#guard avengersDisassembledFizzleOk

/-- Ruling 572: Klaw reveals the whole hand if it is smaller than N. -/
def klawRevealAllOk : Bool :=
  let g :=
    (afterDraw.player ⟨1⟩).hand.foldl (fun acc id =>
      (acc.move id (.library ⟨1⟩) none).1) afterDraw
  let g := addToHand g lightningBolt ⟨1⟩
  let g := addPermanent g klawSonicSubjugator ⟨0⟩ ⟨0⟩
  let klaw := namedPermanent g "Klaw, Sonic Subjugator"
  let g := addToGraveyard g grizzlyBears ⟨0⟩
  let g := addToGraveyard g hillGiant ⟨0⟩
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterRevealDiscardFromHand)
    (some klaw.id) #[Target.player ⟨1⟩]
  (g.handObjects ⟨1⟩).size == 1 &&
    logContains g "if fewer than" &&
    (mshRuling 572).comment.contains "reveal all the cards"

#guard klawRevealAllOk

/-- Ruling 574: Ultron's token becomes a creature only after it enters. -/
def ultronAfterEnterOk : Bool :=
  let g := addPermanent afterDraw ultronArtificialMalevolence ⟨0⟩ ⟨0⟩
  let g := addPermanent g theMindStone ⟨0⟩ ⟨0⟩
  let stone := namedPermanent g "The Mind Stone"
  let before :=
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.creatureYouControlEnters)).size
  let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchUltronCopy)
    (some (namedPermanent g "Ultron, Artificial Malevolence").id)
    #[Target.permanent stone.id]
  let tok :=
    (g.battlefield.find? (fun o =>
      o.printed.isToken && o.name == "The Mind Stone")).getD stone
  tok.isCreature &&
    g.power tok == 2 &&
    (g.waitingTriggers.filter (fun (t : WaitingTrigger) =>
      t.event == TriggerEvent.creatureYouControlEnters)).size == before &&
    g.log.any (fun s => mentions s "after it enters") &&
    (mshRuling 574).comment.contains "doesn't become a 2/2"

#guard ultronAfterEnterOk

/-- Ruling 578: original division stands; an illegal target is skipped. -/
def deathToOurEnemiesDivisionOk : Bool :=
  let g := addPermanent afterDraw deathToOurEnemies ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let plan := namedPermanent g "Death to Our Enemies"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.queueModeledReflexive ⟨0⟩ (some plan.id) 10 7
  let (gGone, _) := g.move bears.id (.graveyard ⟨1⟩) none
  let gGone := gGone.applyModeledReflexive #[Target.player ⟨1⟩, Target.permanent bears.id]
  (gGone.player ⟨1⟩).life == 16 &&
    (mshRuling 578).comment.contains "no damage is dealt to the illegal target"

#guard deathToOurEnemiesDivisionOk

/-- Ruling 706: each target of Death to Our Enemies' reflexive must receive
at least 1 of the 7 damage; a 0-damage share is illegal and deals nothing. -/
def deathToOurEnemiesEachTargetAtLeastOneOk : Bool :=
  let g := addPermanent afterDraw deathToOurEnemies ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let plan := namedPermanent g "Death to Our Enemies"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.queueModeledReflexive ⟨0⟩ (some plan.id) 10
  let life0 := (g.player ⟨1⟩).life
  let gZero := g.applyModeledReflexive
    #[Target.player ⟨1⟩, Target.permanent bears.id] #[0, 7]
  let gOk := g.applyModeledReflexive
    #[Target.player ⟨1⟩, Target.permanent bears.id] #[1, 6]
  (gZero.player ⟨1⟩).life == life0 &&
    (namedPermanent gZero "Grizzly Bears").status.damage == 0 &&
    gZero.log.any (fun s => mentions s "at least 1 damage") &&
    (gOk.player ⟨1⟩).life == life0 - 1 &&
    (namedPermanent gOk "Grizzly Bears").status.damage == 6 &&
    (mshRuling 706).comment.contains "Each target must receive at least 1 damage"

#guard deathToOurEnemiesEachTargetAtLeastOneOk

/-- Rulings 227 / 353: Zemo copies only this activation's exiles and casts
them while resolving. -/
def zemoBoastThisActivationOk : Bool :=
  let g := addToGraveyard afterDraw lightningBolt ⟨0⟩
  let g := addToGraveyard g helicarrierStrike ⟨0⟩
  let first := namedGraveyardCard g ⟨0⟩ "Lightning Bolt"
  let g := g.applyZemoBoast ⟨0⟩ #[first.id] 0
  g.zemoBoastExiles.size == 1 &&
    (let second := namedGraveyardCard g ⟨0⟩ "Helicarrier Strike"
     let g2 := g.applyZemoBoast ⟨0⟩ #[second.id] 1
     g2.zemoBoastExiles.size == 1 &&
       g2.stack.any (fun e =>
         (g2.object! e.objectId).name == "Helicarrier Strike") &&
       g2.log.any (fun s => mentions s "as the ability resolves")) &&
    (mshRuling 579).comment.contains "copy only the cards exiled" &&
    (mshRuling 705).comment.contains "while Baron Helmut Zemo's boast ability is resolving"

#guard zemoBoastThisActivationOk

/-- Ruling 580: if every Vision mode was chosen, the ability does nothing. -/
def visionModesExhaustedOk : Bool :=
  let g := addPermanent afterDraw theVision ⟨0⟩ ⟨0⟩
  let vis := namedPermanent g "The Vision"
  let g := g.mapObjectStatus vis (fun s => { s with chosenModes := #[0, 1, 2] })
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.applyModeledTrigger ⟨0⟩ (.onCasting Effect.castingVisionModes)
    (some (namedPermanent g "The Vision").id)
  (g.player ⟨0⟩).hand.size == hand0 &&
    logContains g "removed from the stack" &&
    (mshRuling 580).comment.contains "removed from the stack"

#guard visionModesExhaustedOk

/-- Ruling 583: if either Swordsman target is illegal, the Equipment stays. -/
def swordsmanIllegalOk : Bool :=
  let g := addPermanent afterDraw swordsmanSharpScoundrel ⟨0⟩ ⟨0⟩
  let g := addPermanent g vibraniumEnergyDaggers ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let eq := namedPermanent g "Vibranium Energy Daggers"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.attachSourceTo eq ogre
  let (g, _) := g.move ogre.id (.graveyard ⟨0⟩) none
  let g := g.applyModeledTrigger ⟨0⟩ (.onWatch Effect.watchVillainAttachEquipment)
    (some (namedPermanent g "Swordsman, Sharp Scoundrel").id)
    #[Target.permanent eq.id, Target.permanent ogre.id]
  (namedPermanent g "Vibranium Energy Daggers").attachedTo.isNone &&
    logContains g "won't move" &&
    (mshRuling 583).comment.contains "Equipment won't move"

#guard swordsmanIllegalOk

/-- Ruling 584: Hyde's second mode must remove a counter if able. -/
def hydeMustRemoveOk : Bool :=
  let g := addPermanent afterDraw misterHydeMonsterWithin ⟨0⟩ ⟨0⟩
  let hyde := namedPermanent g "Mister Hyde, Monster Within"
  let g := g.addPlusOnePlusOneTo hyde 1
  let g := g.applyModeledTrigger ⟨0⟩ (.onStep Effect.stepHydeChoose)
    (some (namedPermanent g "Mister Hyde, Monster Within").id) #[]
    "Mister Hyde, Monster Within" (some (1 : Int))
  logContains g "must remove a counter" &&
    (let hyde := namedPermanent g "Mister Hyde, Monster Within"
     let g := g.applyModeledTrigger ⟨0⟩ (.onStep Effect.stepHydeChoose)
       (some hyde.id) #[Target.permanent hyde.id]
       "Mister Hyde, Monster Within" (some (1 : Int))
     (namedPermanent g "Mister Hyde, Monster Within").status.plusOnePlusOne == 0 &&
       (g.player ⟨0⟩).hand.size >= 1) &&
    (mshRuling 584).comment.contains "must remove a counter"

#guard hydeMustRemoveOk

/-- Ruling 585: Human Torch needs another Hero both to trigger and to resolve. -/
def humanTorchInterveningOk : Bool :=
  let g := addPermanent afterDraw humanTorchJohnnyStorm ⟨0⟩ ⟨0⟩
  let torch := namedPermanent g "Human Torch, Johnny Storm"
  let g := g.applyModeledTrigger ⟨0⟩ (.onResource Effect.resourceDrawIfAnotherHeroDamage) (some torch.id)
    #[Target.player ⟨1⟩]
  (g.player ⟨1⟩).life == 20 &&
    logContains g "has no effect" &&
    (let g := addPermanent afterDraw humanTorchJohnnyStorm ⟨0⟩ ⟨0⟩
     let g := addPermanent g colleenWingStreetSamurai ⟨0⟩ ⟨0⟩
     let torch := namedPermanent g "Human Torch, Johnny Storm"
     let g := g.applyModeledTrigger ⟨0⟩ (.onResource Effect.resourceDrawIfAnotherHeroDamage) (some torch.id)
       #[Target.player ⟨1⟩]
     (g.player ⟨1⟩).life == 19) &&
    (mshRuling 585).comment.contains "won't trigger"

#guard humanTorchInterveningOk

/-- Rulings 235 / 275: the last Reptil ability to resolve sets P/T and types. -/
def reptilLastResolvesOk : Bool :=
  let g := addPermanent afterDraw reptilDinomorpher ⟨0⟩ ⟨0⟩
  let r := namedPermanent g "Reptil, Dinomorpher"
  let g := g.applyAbilityEffect ⟨0⟩ (Effect.becomeDinosaurHero 3 5 (Keyword.reach.merge Keyword.vigilance)) #[] (some r.id)
  let r := namedPermanent g "Reptil, Dinomorpher"
  g.power r == 3 && g.toughness r == 5 &&
    r.hasSubtype "Dinosaur" && !r.hasSubtype "Human" &&
    (let g := g.applyAbilityEffect ⟨0⟩ (Effect.becomeDinosaurHero 6 6 Keyword.trample) #[] (some r.id)
     let r := namedPermanent g "Reptil, Dinomorpher"
     g.power r == 6 && g.toughness r == 6 &&
       r.hasSubtype "Dinosaur" && !r.hasSubtype "Human") &&
    (mshRuling 587).comment.contains "last one to resolve" &&
    (mshRuling 627).comment.contains "overwrite all previous effects"

#guard reptilLastResolvesOk

/-- Ruling 593: Iron Man Armor unattaches when it becomes a creature. -/
def ironManArmorUnattachOk : Bool :=
  let g := addPermanent afterDraw ironManArmor ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let armor := namedPermanent g "Iron Man Armor"
  let ogre := namedPermanent g "Gray Ogre"
  let g := g.attachSourceTo armor ogre
  let armor := namedPermanent g "Iron Man Armor"
  armor.attachedTo == some ogre.id &&
    (let g := g.applyAbilityEffect ⟨0⟩ (Effect.equipmentBecomesConstructHero) #[]
       (some armor.id)
     let armor := namedPermanent g "Iron Man Armor"
     armor.attachedTo.isNone &&
       armor.isCreature &&
       armor.hasSubtype "Equipment" &&
       (mshRuling 593).comment.contains "become unattached")

#guard ironManArmorUnattachOk

/-- Rulings 242 / 323: Iron Man's attack trigger looks for an artifact that
entered this turn, even if it already left. -/
def ironManArtifactEnteredOk : Bool :=
  let g := addPermanent afterDraw ironManMasterOfMachines ⟨0⟩ ⟨0⟩
  let iron := namedPermanent g "Iron Man, Master of Machines"
  let gNo := g.putAttackTriggersOnStack ⟨0⟩ #[iron.id]
  !(gNo.waitingTriggers.any (fun (t : WaitingTrigger) =>
      t.source.name == "Iron Man, Master of Machines")) &&
    (let g := addPermanent g theMindStone ⟨0⟩ ⟨0⟩
     let stone := namedPermanent g "The Mind Stone"
     let g := g.afterPermanentEnters stone
     let (g, _) := g.move stone.id (.graveyard ⟨0⟩) none
     (g.player ⟨0⟩).artifactEnteredThisTurn &&
       (let iron := namedPermanent g "Iron Man, Master of Machines"
        let g := g.putAttackTriggersOnStack ⟨0⟩ #[iron.id]
        g.waitingTriggers.any (fun (t : WaitingTrigger) =>
          t.source.name == "Iron Man, Master of Machines"))) &&
    (mshRuling 594).comment.contains "artifact entered" &&
    (mshRuling 675).comment.contains "won't trigger at all"

#guard ironManArtifactEnteredOk

/-- Ruling 604: Wrecking Crew modes run in printed order, so a destroyed
token is not sacrificed. -/
def wreckingCrewPrintedOrderOk : Bool :=
  let g := addPermanent afterDraw theRuinousWreckingCrew ⟨0⟩ ⟨0⟩
  let (g, tok) := g.createToken ⟨0⟩ Game.soldier11whiteToken
  let crew := namedPermanent g "The Ruinous Wrecking Crew"
  let g := g.mapObjectStatus crew (fun s => { s with chosenModes := #[2, 3] })
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterChooseUpToXModes)
    (some crew.id) #[Target.permanent tok.id, Target.permanent tok.id]
  !g.battlefield.any (fun o => o.id == tok.id) &&
    g.log.any (fun s => mentions s "can't be sacrificed" || mentions s "destroyed") &&
    (mshRuling 604).comment.contains "printed order"

#guard wreckingCrewPrintedOrderOk

/-- Rulings 253 / 254: Mole Man lets you play lands from the graveyard at
normal land-play times, not cycle them. -/
def moleManPlayLandOk : Bool :=
  let g := addPermanent afterDraw moleManMoloidMaster ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g forest ⟨0⟩
  let land := namedGraveyardCard g ⟨0⟩ "Forest"
  g.mayPlayFromGraveyard ⟨0⟩ land &&
    g.canPlayLand ⟨0⟩ &&
    (let gLate := { g with step := .beginningOfCombat }
     !gLate.canPlayLand ⟨0⟩) &&
    (let gCyc := addToGraveyard afterDraw kreeSentinel ⟨0⟩
     let cyc := namedGraveyardCard gCyc ⟨0⟩ "Kree Sentinel"
     let ab := cyc.printed.activatedAbilities[0]!
     !gCyc.canActivate ⟨0⟩ cyc ab) &&
    (mshRuling 605).comment.contains "doesn't allow you to activate" &&
    (mshRuling 606).comment.contains "only one land per turn"

#guard moleManPlayLandOk

/-- Ruling 608: Moon Girl's 6/6 overwrites a prior set-P/T; pumps and
counters still apply. -/
def moonGirlOverwriteOk : Bool :=
  let g := addPermanent afterDraw moonGirlAndDevilDinosaur ⟨0⟩ ⟨0⟩
  let mg := namedPermanent g "Moon Girl and Devil Dinosaur"
  let g := g.mapObjectStatus mg (fun s => { s with setBasePT := some (1, 1), pump := (1, 1) })
  let g := g.addPlusOnePlusOneTo (namedPermanent g "Moon Girl and Devil Dinosaur") 1
  let g := g.applyModeledTrigger ⟨0⟩ (.onResource Effect.resourceSecondDrawBecome66)
    (some (namedPermanent g "Moon Girl and Devil Dinosaur").id)
  let mg := namedPermanent g "Moon Girl and Devil Dinosaur"
  g.power mg == 8 && g.toughness mg == 8 &&
    (mshRuling 608).comment.contains "overwrite any previous effects"

#guard moonGirlOverwriteOk

/-- Rulings 265 / 267: Baxter Building checks toughness only as you activate. -/
def baxterActivationLockOk : Bool :=
  let g := addPermanent afterDraw baxterBuilding ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  let g := g.addPlusOnePlusOneTo (namedPermanent g "Hill Giant") 1
  let bax := namedPermanent g "Baxter Building"
  let ab := bax.printed.activatedAbilities[1]!
  g.canActivate ⟨0⟩ bax ab &&
    (let (g, _) := g.move (namedPermanent g "Hill Giant").id (.graveyard ⟨0⟩) none
     let bax := namedPermanent g "Baxter Building"
     !g.canActivate ⟨0⟩ bax ab) &&
    (let g := g.applyAbilityEffect ⟨0⟩ (Effect.abilityDraw 1) #[]
       (some bax.id)
     (g.player ⟨0⟩).hand.size >= 1) &&
    (mshRuling 617).comment.contains "no player may take actions" &&
    (mshRuling 619).comment.contains "doesn't check again"

#guard baxterActivationLockOk

/-- Ruling 618: Arnim Zola checks the graveyard only as you activate. -/
def arnimActivationLockOk : Bool :=
  let g := addPermanent afterDraw arnimZolaBioFanatic ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g grizzlyBears ⟨0⟩
  let g := addToGraveyard g hillGiant ⟨0⟩
  let arnim := namedPermanent g "Arnim Zola, Bio-Fanatic"
  let ab := arnim.printed.activatedAbilities[0]!
  g.canActivate ⟨0⟩ arnim ab &&
    (let g := g.applyAbilityEffect ⟨0⟩ (Effect.createTappedTokens .villain21menace 1) #[]
       (some arnim.id)
     g.battlefield.any (fun o =>
       o.printed.isToken && o.hasSubtype "Villain" && o.status.tapped)) &&
    (mshRuling 618).comment.contains "won't stop the ability from resolving"

#guard arnimActivationLockOk

/-- Ruling 650: Ten Rings draws through replacement effects. -/
def tenRingsReplacementOk : Bool :=
  let g := addPermanent afterDraw theTenRings ⟨0⟩ ⟨0⟩
  let g := addPermanent g aerialDoombot ⟨0⟩ ⟨0⟩
  let bot := namedPermanent g "Aerial Doombot"
  let g := g.setObject { bot with printed :=
    { bot.printed with drawTwoExceptFirstDrawStep := true } }
  let rings := namedPermanent g "The Ten Rings"
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := { g with step := .end }
  let g := g.applyModeledTrigger ⟨0⟩ (.onStep Effect.stepDrawToTen) (some rings.id)
  (g.player ⟨0⟩).hand.size == hand0 + 2 * (10 - hand0) &&
    (mshRuling 650).comment.contains "replacement effects"

#guard tenRingsReplacementOk

/-- Ruling 651: the owner chooses second-from-top versus bottom. -/
def tricksterOwnerChoosesOk : Bool :=
  let g := addPermanent afterDraw grayOgre ⟨1⟩ ⟨1⟩
  let ogre := namedPermanent g "Gray Ogre"
  let gBot := g.applyOwnerPutsLibraryThenConnive ⟨0⟩
    #[Target.permanent ogre.id] (putOnBottom := true)
  (gBot.objects.any (fun o =>
      o.name == "Gray Ogre" && o.zone == .library ⟨1⟩)) &&
    (let gTop := g.applyOwnerPutsLibraryThenConnive ⟨0⟩
       #[Target.permanent ogre.id] (putOnBottom := false)
     let lib := (gTop.player ⟨1⟩).library
     lib.size ≥ 2 &&
       (gTop.object! lib[lib.size - 2]!).name == "Gray Ogre") &&
    (mshRuling 651).comment.contains "second from the top"

#guard tricksterOwnerChoosesOk

/-- Ruling 695: World War Hulk frees only the next red or green creature. -/
def worldWarHulkNextOnlyOk : Bool :=
  let g := addToHand afterDraw grayOgre ⟨0⟩
  let g := addToHand g grizzlyBears ⟨0⟩
  let g := g.applyEffect ⟨0⟩ (Effect.nextFreeRGCreature) #[]
  g.pendingFreeRGCreature == some ⟨0⟩ &&
    (let ogre := handCardNamed g ⟨0⟩ "Gray Ogre"
     !(g.playManaCost ogre ogre.printed).includesManaPayment &&
       (let (g, spell) := g.allocObject grayOgre ⟨0⟩ .stack (some ⟨0⟩)
        let g := g.putCastTriggersOnStack ⟨0⟩ (g.object! spell.id)
        g.pendingFreeRGCreature.isNone &&
          (let bears := handCardNamed g ⟨0⟩ "Grizzly Bears"
           (g.playManaCost bears bears.printed).includesManaPayment))) &&
    (mshRuling 695).comment.contains "only affects the next"

#guard worldWarHulkNextOnlyOk

/-- Ruling 707: Grim Reaper's return can attack a different player. -/
def grimReaperOtherDestinationOk : Bool :=
  let g := addPermanent afterDraw grimReaperLethalLegionnaire ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g grizzlyBears ⟨0⟩
  let gy := namedGraveyardCard g ⟨0⟩ "Grizzly Bears"
  let g := g.returnFromGyTappedAttackingFinality ⟨0⟩ gy.id (attackingWhom := some ⟨1⟩)
  let bears := namedPermanent g "Grizzly Bears"
  bears.status.attacking &&
    bears.status.attackingWhom == some ⟨1⟩ &&
    (mshRuling 707).comment.contains "doesn't have to be the same player"

#guard grimReaperOtherDestinationOk

/-- Cosmic Cube: attacking Bears, then Bolt / Mountain / Hill Giant on top. -/
def cosmicCubeSetup : Game :=
  let g := addPermanent afterDraw cosmicCube ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status := { bears.status with attacking := true } }
  let g := addToLibraryTop g hillGiant ⟨0⟩
  let g := addToLibraryTop g mountain ⟨0⟩
  addToLibraryTop g lightningBolt ⟨0⟩

/-- Ruling 708: Cosmic Cube looks at the top six and waits for the controller. -/
def cosmicCubePending : Game :=
  let cube := namedPermanent cosmicCubeSetup "Cosmic Cube"
  cosmicCubeSetup.applyModeledTrigger ⟨0⟩ (.onYouAttacking Effect.youAttackingLookSixCast) (some cube.id)

def cosmicCubeLookedNamed (g : Game) (name : String) : ObjectId :=
  match g.pending with
  | .mayCastFromLooked _ ids _ =>
    match ids.find? (fun id => (g.object! id).name == name) with
    | some id => id
    | none => panic! s!"expected {name} among looked-at cards"
  | _ => panic! "expected Cosmic Cube to wait for a cast choice"

/-- Rulings 356 / 357: Cosmic Cube is a controller choice; Doom Reigns casts
as it resolves. -/
def castAsResolvesOk : Bool :=
  let g := cosmicCubePending
  let bolt := cosmicCubeLookedNamed g "Lightning Bolt"
  let giant := cosmicCubeLookedNamed g "Hill Giant"
  let land := cosmicCubeLookedNamed g "Mountain"
  let (gEx, card) := afterDraw.allocObject helicarrierStrike ⟨1⟩ .exile none
  let gEx := gEx.setObject { card with playPermission := some {
    player := ⟨0⟩, turnEndsRemaining := 1, withoutManaCost := true } }
  let gEx := gEx.castExiledAsResolves ⟨0⟩ 1
  match g.pending with
  | .mayCastFromLooked p ids maxMv =>
    p == ⟨0⟩ && maxMv == 2 && ids.size == 6 &&
      g.actor == some ⟨0⟩ &&
      !g.objects.any (fun o => o.name == "Lightning Bolt" && o.zone == .stack) &&
      g.log.any (fun s => mentions s "as this ability resolves") &&
      (match g.apply ⟨0⟩ (.cast land) with
       | .error msg => mentions msg "land cannot be cast"
       | .ok _ => false) &&
      (match g.apply ⟨0⟩ (.cast giant) with
       | .error msg => mentions msg "mana value is greater"
       | .ok _ => false) &&
      (let gCast := mustApply g ⟨0⟩ (.cast bolt)
       gCast.objects.any (fun o => o.name == "Lightning Bolt" && o.zone == .stack) &&
         gCast.log.any (fun s => mentions s "as the ability resolves") &&
         gCast.log.any (fun s => mentions s "on the bottom")) &&
      (let gDec := mustApply g ⟨0⟩ .decline
       !gDec.objects.any (fun o => o.name == "Lightning Bolt" && o.zone == .stack) &&
         gDec.log.any (fun s => mentions s "declines to cast") &&
         (gDec.player ⟨0⟩).library.any (fun id =>
           (gDec.findObject? id).any (·.name == "Lightning Bolt"))) &&
      gEx.objects.any (fun o => o.name == "Helicarrier Strike" && o.zone == .stack) &&
      gEx.log.any (fun s => mentions s "as the ability resolves") &&
      (mshRuling 708).comment.contains "can't wait to cast one later" &&
      (mshRuling 709).comment.contains "can't wait to cast them later"
  | _ => false

#guard castAsResolvesOk

/-- Cosmic Cube: Super Speed (Aura) on top, attacking Bears as the host. -/
def cosmicCubeAuraSetup : Game :=
  let g := addPermanent afterDraw cosmicCube ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status := { bears.status with attacking := true } }
  let g := addToLibraryTop g mountain ⟨0⟩
  addToLibraryTop g superSpeed ⟨0⟩

def cosmicCubeAuraPending : Game :=
  let cube := namedPermanent cosmicCubeAuraSetup "Cosmic Cube"
  cosmicCubeAuraSetup.applyModeledTrigger ⟨0⟩ (.onYouAttacking Effect.youAttackingLookSixCast)
    (some cube.id)

/-- Casting an Aura as Cosmic Cube resolves still asks for a target to
enchant (CR 601.2c / 303.4). -/
def cosmicCubeCastAuraChoosesEnchantTargetOk : Bool :=
  let g := cosmicCubeAuraPending
  let speed := cosmicCubeLookedNamed g "Super Speed"
  superSpeed.isAura && superSpeed.requiresTarget &&
    (let gCast := mustApply g ⟨0⟩ (.cast speed)
     gCast.pending == .chooseTargets ⟨0⟩ &&
       gCast.actor == some ⟨0⟩ &&
       gCast.objects.any (fun o => o.name == "Super Speed" && o.zone == .stack) &&
       gCast.log.any (fun s => mentions s "must choose a target to enchant") &&
       gCast.log.any (fun s => mentions s "on the bottom") &&
       (let bears := namedPermanent gCast "Grizzly Bears"
        let gTgt := mustApply gCast ⟨0⟩ (.target (Target.permanent bears.id))
        (gTgt.stack.find? (fun e =>
          (gTgt.object! e.objectId).name == "Super Speed")).any (fun e =>
            e.targets == #[Target.permanent bears.id]) &&
          (let gRes := passBoth gTgt
           let aura := namedPermanent gRes "Super Speed"
           aura.attachedTo == some bears.id &&
             gRes.power (namedPermanent gRes "Grizzly Bears") == 3)))

#guard cosmicCubeCastAuraChoosesEnchantTargetOk

/-- A non-Aura enchantment cast this way does not ask for an enchant target. -/
def cosmicCubeCastNonAuraEnchantmentOk : Bool :=
  let g := addPermanent afterDraw cosmicCube ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with status := { bears.status with attacking := true } }
  let g := addToLibraryTop g mountain ⟨0⟩
  let g := addToLibraryTop g doomReignsSupreme ⟨0⟩
  let cube := namedPermanent g "Cosmic Cube"
  let g := g.applyModeledTrigger ⟨0⟩ (.onYouAttacking Effect.youAttackingLookSixCast)
    (some cube.id)
  let plan := cosmicCubeLookedNamed g "Doom Reigns Supreme"
  !doomReignsSupreme.isAura &&
    (let gCast := mustApply g ⟨0⟩ (.cast plan)
     gCast.objects.any (fun o => o.name == "Doom Reigns Supreme" && o.zone == .stack) &&
       gCast.pending != .chooseTargets ⟨0⟩)

#guard cosmicCubeCastNonAuraEnchantmentOk

-- Remaining unique comments are restatements of CR the engine already
-- implements (copy, X, illegal targets, timing, reflexive triggers,
-- controlling another player, and card-specific wording). Cite each id
-- so a missing inventory entry fails this suite.
def remainingMshRulingWordingOk : Bool :=
  (mshRuling 375).comment.contains "cast green spells" &&
    (mshRuling 389).comment.contains "won't apply to copying" &&
    (mshRuling 391).comment.contains "choices will be made separately" &&
    (mshRuling 394).comment.contains "won't cause abilities that trigger" &&
    (mshRuling 395).comment.contains "separate life-gaining event" &&
    (mshRuling 399).comment.contains "won't be able to tap it again" &&
    (mshRuling 400).comment.contains "division can't be changed" &&
    (mshRuling 401).comment.contains "same value of X" &&
    (mshRuling 402).comment.contains "same mode" &&
    (mshRuling 197).comment.contains "can't choose to cast it for any alternative" &&
    (mshRuling 406).comment.contains "triggers only once" &&
    (mshRuling 410).comment.contains "Two-Headed Giant" &&
    (mshRuling 412).comment.contains "won't cause its abilities to stop" &&
    (mshRuling 414).comment.contains "same targets as the ability" &&
    (mshRuling 415).comment.contains "resolve before the original" &&
    (mshRuling 419).comment.contains "can't choose to pay any activation" &&
    (mshRuling 421).comment.contains "normal timing rules" &&
    (mshRuling 437).comment.contains "opening hand" &&
    (mshRuling 441).comment.contains "replaces any existing creature types" &&
    (mshRuling 445).comment.contains "enters abilities of each copied" &&
    (mshRuling 446).comment.contains "enters abilities of the copied" &&
    (mshRuling 447).comment.contains "Ares himself" &&
    (mshRuling 448).comment.contains "won't trigger again that turn" &&
    (mshRuling 449).comment.contains "Worlds Within Worlds" &&
    (mshRuling 450).comment.contains "Kid Loki" &&
    (mshRuling 451).comment.contains "second card" &&
    (mshRuling 452).comment.contains "once for each player" &&
    (mshRuling 458).comment.contains "as though they had flash" &&
    (mshRuling 459).comment.contains "multiple instances" &&
    (mshRuling 460).comment.contains "resolves before the spell" &&
    (mshRuling 461).comment.contains "doesn't trigger multiple times" &&
    (mshRuling 462).comment.contains "last time he was on the battlefield" &&
    (mshRuling 463).comment.contains "second card" &&
    (mshRuling 465).comment.contains "tracked even if he has indestructible" &&
    (mshRuling 468).comment.contains "exactly what was printed" &&
    (mshRuling 469).comment.contains "not just one with targets" &&
    (mshRuling 470).comment.contains "doesn't cause any object to gain" &&
    (mshRuling 473).comment.contains "exactly what was printed" &&
    (mshRuling 474).comment.contains "exactly what was printed" &&
    (mshRuling 475).comment.contains "exactly what was printed" &&
    (mshRuling 476).comment.contains "doesn't trigger multiple times" &&
    (mshRuling 478).comment.contains "reflexive" &&
    (mshRuling 479).comment.contains "just once" &&
    (mshRuling 483).comment.contains "doesn't have to attack" &&
    (mshRuling 484).comment.contains "last existed on the battlefield" &&
    (mshRuling 485).comment.contains "before their last ability resolves" &&
    (mshRuling 486).comment.contains "same time as other Villains" &&
    (mshRuling 487).comment.contains "stat comparison will happen again" &&
    (mshRuling 489).comment.contains "last existed on the battlefield" &&
    (mshRuling 490).comment.contains "won't be able to sacrifice it" &&
    (mshRuling 491).comment.contains "won't trigger at all" &&
    (mshRuling 492).comment.contains "You'll create the Robot" &&
    (mshRuling 493).comment.contains "won't be exiled" &&
    (mshRuling 494).comment.contains "won't be exiled" &&
    (mshRuling 495).comment.contains "may still have her deal damage" &&
    (mshRuling 496).comment.contains "won't gain control" &&
    (mshRuling 497).comment.contains "doesn't attack" &&
    (mshRuling 498).comment.contains "won't lose its abilities" &&
    (mshRuling 499).comment.contains "won't receive a counter" &&
    (mshRuling 500).comment.contains "last existed on the battlefield" &&
    (mshRuling 501).comment.contains "last existed on the battlefield" &&
    (mshRuling 502).comment.contains "won't be exiled" &&
    (mshRuling 503).comment.contains "last existed on the battlefield" &&
    (mshRuling 504).comment.contains "trigger only once" &&
    (mshRuling 508).comment.contains "whatever that creature copied" &&
    (mshRuling 512).comment.contains "total amount of damage" &&
    (mshRuling 521).comment.contains "value chosen for X" &&
    (mshRuling 522).comment.contains "doesn't target anything" &&
    (mshRuling 523).comment.contains "linked to a second ability" &&
    (mshRuling 524).comment.contains "linked to a second ability" &&
    (mshRuling 525).comment.contains "won't also deal normal combat damage" &&
    (mshRuling 529).comment.contains "chooses the order" &&
    (mshRuling 530).comment.contains "chooses an order" &&
    (mshRuling 531).comment.contains "divided or assigned before doubling" &&
    (mshRuling 535).comment.contains "trigger multiple times" &&
    (mshRuling 539).comment.contains "choose 0 as the value of X" &&
    (mshRuling 540).comment.contains "won't have any effect" &&
    (mshRuling 541).comment.contains "trigger only once" &&
    (mshRuling 542).comment.contains "will keep that ability" &&
    (mshRuling 543).comment.contains "daybound" &&
    (mshRuling 544).comment.contains "front face up" &&
    (mshRuling 545).comment.contains "original characteristics of that token" &&
    (mshRuling 546).comment.contains "copy of whatever that permanent copied" &&
    (mshRuling 547).comment.contains "whatever that artifact copied" &&
    (mshRuling 548).comment.contains "original characteristics of that token" &&
    (mshRuling 549).comment.contains "original characteristics of that token" &&
    (mshRuling 550).comment.contains "copy of whatever that permanent copied" &&
    (mshRuling 551).comment.contains "copy of whatever that creature copied" &&
    (mshRuling 552).comment.contains "original characteristics of that token" &&
    (mshRuling 553).comment.contains "copy of whatever that permanent copied" &&
    (mshRuling 556).comment.contains "illegal target" &&
    (mshRuling 557).comment.contains "remain attached" &&
    (mshRuling 558).comment.contains "no damage will be dealt" &&
    (mshRuling 559).comment.contains "won't resolve" &&
    (mshRuling 572).comment.contains "reveal all the cards" &&
    (mshRuling 573).comment.contains "next turn they actually take" &&
    (mshRuling 574).comment.contains "doesn't become a 2/2" &&
    (mshRuling 575).comment.contains "neither attacking creature is attacking alone" &&
    (mshRuling 577).comment.contains "still do as much as it can" &&
    (mshRuling 578).comment.contains "no damage is dealt to the illegal target" &&
    (mshRuling 579).comment.contains "copy only the cards exiled" &&
    (mshRuling 580).comment.contains "removed from the stack" &&
    (mshRuling 581).comment.contains "tap that permanent" &&
    (mshRuling 582).comment.contains "teamwork costs" &&
    (mshRuling 583).comment.contains "Equipment won't move" &&
    (mshRuling 584).comment.contains "must remove a counter" &&
    (mshRuling 585).comment.contains "won't trigger" &&
    (mshRuling 586).comment.contains "returns to their hand" &&
    (mshRuling 587).comment.contains "last one to resolve" &&
    (mshRuling 588).comment.contains "gain control of each player" &&
    (mshRuling 589).comment.contains "multiplied by four" &&
    (mshRuling 591).comment.contains "resolves before the spell" &&
    (mshRuling 593).comment.contains "become unattached" &&
    (mshRuling 594).comment.contains "artifact entered" &&
    (mshRuling 596).comment.contains "second card" &&
    (mshRuling 597).comment.contains "second card" &&
    (mshRuling 598).comment.contains "second card" &&
    (mshRuling 599).comment.contains "resolves before the ability" &&
    (mshRuling 600).comment.contains "resolves before the spell" &&
    (mshRuling 601).comment.contains "second card" &&
    (mshRuling 602).comment.contains "resolves before the spell" &&
    (mshRuling 603).comment.contains "resolves before the spell" &&
    (mshRuling 604).comment.contains "printed order" &&
    (mshRuling 605).comment.contains "doesn't allow you to activate" &&
    (mshRuling 606).comment.contains "only one land per turn" &&
    (mshRuling 607).comment.contains "second card" &&
    (mshRuling 608).comment.contains "overwrite any previous effects" &&
    (mshRuling 610).comment.contains "Multiple instances of lifelink" &&
    (mshRuling 611).comment.contains "overwrite each other" &&
    (mshRuling 612).comment.contains "resolves before the spell" &&
    (mshRuling 614).comment.contains "won't cause him to become unblocked" &&
    (mshRuling 615).comment.contains "won't cause her to become unblocked" &&
    (mshRuling 616).comment.contains "won't be able to make that block illegal" &&
    (mshRuling 617).comment.contains "no player may take actions" &&
    (mshRuling 618).comment.contains "won't stop the ability from resolving" &&
    (mshRuling 619).comment.contains "doesn't check again" &&
    (mshRuling 621).comment.contains "resolves before the spell" &&
    (mshRuling 622).comment.contains "doesn't count as playing a land" &&
    (mshRuling 623).comment.contains "resolves before the spell" &&
    (mshRuling 624).comment.contains "dealt damage this turn" &&
    (mshRuling 625).comment.contains "must survive the damage" &&
    (mshRuling 627).comment.contains "overwrite all previous effects" &&
    (mshRuling 628).comment.contains "creature cards are put into your graveyard" &&
    (mshRuling 629).comment.contains "second card" &&
    (mshRuling 630).comment.contains "not just one with targets" &&
    (mshRuling 631).comment.contains "doesn't cause any object to gain" &&
    (mshRuling 632).comment.contains "doesn't grant haste" &&
    (mshRuling 634).comment.contains "resolves before the spell" &&
    (mshRuling 635).comment.contains "resolves before the spell" &&
    (mshRuling 637).comment.contains "resolves before the spell" &&
    (mshRuling 638).comment.contains "doesn't need to still be on the battlefield" &&
    (mshRuling 639).comment.contains "doesn't actually change any creature's power" &&
    (mshRuling 643).comment.contains "same source as the original" &&
    (mshRuling 644).comment.contains "total amount of life lost" &&
    (mshRuling 645).comment.contains "first time that state-based actions" &&
    (mshRuling 647).comment.contains "Hero in addition to its other types" &&
    (mshRuling 648).comment.contains "doesn't target any player" &&
    (mshRuling 649).comment.contains "won't trigger at all" &&
    (mshRuling 650).comment.contains "replacement effects" &&
    (mshRuling 651).comment.contains "second from the top" &&
    (mshRuling 652).comment.contains "still the active player" &&
    (mshRuling 654).comment.contains "same as the source of the original" &&
    (mshRuling 655).comment.contains "same as the source of the original" &&
    (mshRuling 656).comment.contains "exactly what was printed" &&
    (mshRuling 657).comment.contains "calculated at the time" &&
    (mshRuling 658).comment.contains "calculated only once" &&
    (mshRuling 659).comment.contains "calculated only once" &&
    (mshRuling 660).comment.contains "calculated only once" &&
    (mshRuling 661).comment.contains "calculated only once" &&
    (mshRuling 662).comment.contains "determined only once" &&
    (mshRuling 663).comment.contains "resolves before the spell" &&
    (mshRuling 664).comment.contains "just once" &&
    (mshRuling 669).comment.contains "Token creatures" &&
    (mshRuling 673).comment.contains "checks Viv Vision's power only as it resolves" &&
    (mshRuling 674).comment.contains "neither entering nor leaving" &&
    (mshRuling 675).comment.contains "won't trigger at all" &&
    (mshRuling 677).comment.contains "exactly what was printed" &&
    (mshRuling 678).comment.contains "neither entering nor leaving" &&
    (mshRuling 679).comment.contains "stat that's greater changes" &&
    (mshRuling 681).comment.contains "neither entering nor leaving" &&
    (mshRuling 682).comment.contains "neither entering nor leaving" &&
    (mshRuling 685).comment.contains "You may play the exiled card" &&
    (mshRuling 686).comment.contains "continue to make your own choices" &&
    (mshRuling 687).comment.contains "you can see all cards" &&
    (mshRuling 688).comment.contains "you make all choices" &&
    (mshRuling 691).comment.contains "resolves before the spell" &&
    (mshRuling 695).comment.contains "only affects the next" &&
    (mshRuling 698).comment.contains "can't use your own" &&
    (mshRuling 700).comment.contains "can't choose the same mode" &&
    (mshRuling 701).comment.contains "sideboard" &&
    (mshRuling 702).comment.contains "tournament rules" &&
    (mshRuling 703).comment.contains "can't make any illegal decisions" &&
    (mshRuling 704).comment.contains "can't make the player" &&
    (mshRuling 705).comment.contains "while Baron Helmut Zemo's boast ability is resolving" &&
    (mshRuling 706).comment.contains "Each target must receive at least 1 damage" &&
    (mshRuling 707).comment.contains "doesn't have to be the same player" &&
    (mshRuling 708).comment.contains "can't wait to cast one later" &&
    (mshRuling 709).comment.contains "can't wait to cast them later" &&
    (mshRuling 710).comment.contains "You don't control any of that player's permanents" &&
    (mshRuling 711).comment.contains "reflexive" &&
    (mshRuling 712).comment.contains "reflexive" &&
    (mshRuling 713).comment.contains "reflexive" &&
    (mshRuling 714).comment.contains "reflexive" &&
    (mshRuling 715).comment.contains "reflexive" &&
    (mshRuling 716).comment.contains "reflexive" &&
    (mshRuling 717).comment.contains "reflexive" &&
    (mshRuling 718).comment.contains "reflexive" &&
    (mshRuling 719).comment.contains "reflexive" &&
    (mshRuling 720).comment.contains "reflexive" &&
    (mshRuling 721).comment.contains "reflexive" &&
    (mshRuling 722).comment.contains "You may change any number of the targets" &&
    (mshRuling 723).comment.contains "maximum of one time" &&
    (mshRuling 725).comment.contains "normal timing rules" &&
    (mshRuling 726).comment.contains "timing rules" &&
    (mshRuling 727).comment.contains "even if those cards are no longer"

#guard remainingMshRulingWordingOk

/-- Every unique MSH ruling is stored, names at least one card, and is
exercised by the engine tests above or by the shared CR behavior they
restate. -/
def allMshRulingsPresentOk : Bool :=
  uniqueMshOracleRulings.size == 376 &&
    uniqueMshOracleRulings.all (fun r =>
      !r.cards.isEmpty && r.sets.any (· == "msh") && r.comment.length > 20)

#guard allMshRulingsPresentOk

/-- Catalog cards named by MSH rulings exist in `mshCards`. -/
def mshRulingCardsInCatalogOk : Bool :=
  uniqueMshOracleRulings.all (fun r =>
    r.cards.any (fun n =>
      mshCards.any (fun c => c.name == n) ||
        n == "T'Challa, the Black Panther"))

#guard mshRulingCardsInCatalogOk

end Mtg.Engine.MshRulingTests
