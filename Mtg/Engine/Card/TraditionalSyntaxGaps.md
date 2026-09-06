# TraditionalCardDefinition conversion gaps

This note records what is missing from the part-based printed-card types in
`Mtg/Engine/Card/Definition.lean` in order to convert every **currently
supported catalog card** that is not yet written as a
`TraditionalCardDefinition`.

Thirty cards that previously had no tagged constructor gap are now spelled
as `TraditionalCardDefinition`. Fourteen others still cannot be spelled;
see [Cards that still cannot convert](#cards-that-still-cannot-convert).
Compiler leftovers in `toCardDef` / `CardAction.compile` are mentioned
when a constructor already exists but cannot express the printed ability
without a new constructor.

## Scope

`Oracle.supportedCatalogCards` is the core vanilla cards plus
`Catalog.hobbitCards`, `Catalog.hobbitEternalCards`, and `Catalog.mshCards`.

| Set | Remaining non-TCD cards |
| --- | ---: |
| The Hobbit (HOB) | 117 |
| The Hobbit Eternal (HOC) | 84 |
| Marvel Super Heroes (MSH) | 227 |
| **Total remaining** | **428** |

All **428** remaining cards have at least one identified constructor gap.
Of the 44 that previously had no tagged gap, **30 are now written as
`TraditionalCardDefinition`** (compiler leftovers in `toCardDef` map them
onto existing engine constructors; `#guard supportedCardsMatchOracle`
holds). The other **14 cannot be spelled** with the current types; closer
reading found constructor gaps the first pass missed (see [Cards that still
cannot convert](#cards-that-still-cannot-convert)).

Evidence for each remaining card is its catalog definition (Oracle text plus
modeled `CardDef` fields, triggered/static/activated constructors, and
`Effect` names) compared with the current constructors of `Range`,
`SetPredicate`, `Selector`, `Trigger`, `Cost`, `Condition`, `Ability`,
`ContinuousEffect`, `CardAction`, and `TraditionalCardDefinition` (including
`CardPart`).

`CardSubtype`, `Keyword`, and `CounterKind` are not in the requested list.
They are still blocking because `CardPart.subtype`, `Ability.keyword`, and
`CardAction.putCounter` are indexed by those inductives. Missing constructors
there are listed under `TraditionalCardDefinition`, `Ability`, and
`CardAction` respectively.

## Current constructors (inventory)

From `Mtg/Engine/Card/Definition.lean` as of this analysis:

- **Range** — `range lo hi` (literal `Nat` bounds).
- **SetPredicate** — `shareCardType`.
- **Selector** — `this`, `source`, `controller`, `target` / `targets` /
  `targetSet`, `not`, `targetReference`, `selected`, `intersection`, `all`,
  `cardType`, `union`, `permanent`, `controlled`, `tapped`, `keyword`,
  `powerAtLeast`, `subtype`, `spell`, `permanentSpell`, `player`, `opponent`,
  `owner`, `attacking`, `blocking`, `token`, `wasObjectOfAction`,
  `replacingObject`, `wasCreatedByAction`, `hostOf`, `inGraveyard`, `inDeck`,
  `supertype`, `variable`, `topOfLibrary`.
- **Trigger** — `endOfGame`, `endOfTurn`, `endOfPlayerTurn`, `turnStart`,
  `gameStart`, `attack`, `enter`, `draw`, `ordinal`, `combatDamage`,
  `putToGraveyard`, `block`, `die`, `dieSimultaneously`,
  `attackSimultaneously` (who attacks, who is attacked),
  `abilityWithIdActivated`, `actionWithId`,
  `spendManaCreatedByAction`, `castSpell`, `activateAbility`, `sequence`,
  `not`, `or`.
- **Cost** — `mana`, `life`, `sacrifice` (every selected permanent),
  `sacrificeCount` (that many matching permanents), `tapSymbol`,
  `discard`, `or`.
- **Condition** — `any`, `targetsIncludeAny`, `anySubtype`, `didNotHappen`,
  `happened`, `timeToCastSorcery`, `turn`, `and`.
- **CardState** — `tapped`, `controlled` (who controls as the permanent enters).
- **Ability** — `keyword`, `keywordWithCost`, `keywordWithSubtypeAndCost`,
  `keywordWithTarget`, `activated`, `activatedIf`, `abilityId`, `triggered`,
  `static`.
- **ContinuousEffect** — `gainAbility`, `addPowerToughness`, `if`,
  `reduceCost`, `additionalCost`, `replace`, `forbid`,
  `canCastWithoutPayingManaCost`, `canPlay`, `setBasePowerToughnessFrom`,
  `gainType`, `gainSubtype`, `setPowerToughnessEqualToCount`,
  `increaseLandPlayLimit`.
- **CardAction** — `continuous`, `tap`, `untap`, `dealDamage`, `divideDamage`,
  `draw`, `scry`, `sequence`, `if`, `optional`, `attach`, `chooseMode`,
  `counter`, `preventable`, `discard`, `putCounter`, `exile`,
  `exchangeControl`, `destroy`, `gainLife`, `playerSelectAction`,
  `putOnTopOfLibrary`, `putOnBottomOfLibrary`, `actionId`, `loseLife`,
  `sacrifice`, `returnToHand`, `putOntoBattlefield`,
  `putOntoBattlefieldInState`, `searchLibraryThenShuffle`,
  `holdOutInLibrary`, `defineVariable`,
  `forEachVariable`, `reveal`, `dealDamageEqualToPower`, `addManaAnyColor`,
  `addManaAnyColorEqualToPower`, `addMana`.
- **TraditionalCardDefinition** — `card : List CardPart`, with `CardPart`
  `name`, `manaCost`, `type`, `supertype`, `subtype`, `power`, `toughness`,
  `ability`, `alternative` (Adventure face), `actions`.

Converted catalog cards (Bofur, Lightning Bolt, Wood Elves, Rogue's Passage,
Gundabad Opportunist, Elvish Mystic, Guttersnipe, Fisk Tower, …) already use
that inventory. Remaining cards need the constructors below.

## Missing constructors by type

Each subsection lists constructors that at least one remaining supported card
needs. Card names are examples; the [per-card index](#per-card-index) is
complete.

### `Range`

- **`computed`** (53 cards) — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
  - An Unexpected Party; Armor Wars; Azog, Moria's Ruin; Balin, Loremaster; Bard, King of Dale; Bolg of the North; Bruce Banner; Call Forth the Tempest; Captain America, Wings of Freedom; Cavern-Hoard Dragon; Ori, Plate Stacker; … (42 more)
- **`anyNumber`** (3 cards) — Any number (range 0 ∞); Range.range needs a finite Nat hi
  - Last March of the Ents; Worlds Within Worlds; Super-Soldier Serum

### `SetPredicate`

- **`distinctNames`** (13 cards) — Set-wide name constraints
  - Avengers Tower; Boughside Wanderers; Cantankerous Keepers; Cosmic Cube; Dáin's Company; Earth's Mightiest Heroes; Getaway Barrel; Glamdring, Foe-hammer; Most Decrepit Old Bird; Nick Fury, Agent of S.H.I.E.L.D.; … (3 more)
- **`shareName`** (1 cards) — The selected objects share a name
  - Key to the Side-Door

### `Selector`

- **`topNOfLibrary`** (30 cards) — The top N cards of a library (only topOfLibrary for N=1 exists)
  - A.I.M. Synthoids; Avengers Tower; Boughside Wanderers; Colleen Wing, Street Samurai; Cosmic Cube; Daredevil, Man Without Fear; Doom Reigns Supreme; Dáin's Company; Earth's Mightiest Heroes; Elven Chorus; Black Widow, Super Spy; … (19 more)
- **`countOf`** (27 cards) — Numeric value derived from a count or characteristic
  - Bolg of the North; Call Forth the Tempest; Cosmic Cube; Desert Were-Worm; Dragon's Desire; Dáin of the Ancient Halls; Esgaroth Garrison; Glamdring; HULK SMASH!; Inside Information; Ori, Plate Stacker; … (16 more)
- **`inHand`** (26 cards) — An object in a hand
  - A.I.M. Scientists; Baron Helmut Zemo; Baron Strucker, HYDRA Overlord; Cloak and Dagger, Entwined; Elven Passage; Errand-Rider of Gondor; Gandalf, Party Guest; Glamdring; Great Gilded Boat; H.E.R.B.I.E. Scout Unit; … (16 more)
- **`manaValue`** (25 cards) — Mana-value comparisons
  - Armor Wars; Bilbo, Unexpected Adventurer; Call Forth the Tempest; Cosmic Cube; Cruel Alliance; Dancing from Dark to Dawn; Evil's Thrall; Gandalf, Party Guest; Glamdring; Gollum, Riddle Master; … (15 more)
- **`eachPlayer`** (23 cards) — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)
  - Armor Wars; Avengers: Under Siege; Balin, Loremaster; Bilbo's Burglaring; Celebrate the Mountain-king; Crossbones, Malicious Mercenary; Doom Reigns Supreme; Dáin of the Ancient Halls; Gandalf, Goblins' Bane; Gollum, Riddle Master; … (13 more)
- **`army`** (15 cards) — Army (CardSubtype.army is also missing; used via Selector.subtype)
  - Azog, Moria's Ruin; Bolg of the North; Bothersome Noisemaker; Down, Down to Goblin-town; Fearsome Goblin Pair; Gathering of Darkness; Goblin Plate Mail; Goblin-town Flunkies; Great Goblin, Foul-Hearted; Misty Mountains Raider; … (5 more)
- **`color`** (14 cards) — Objects of a color / colorless
  - Aragorn, the Uniter; Baron Helmut Zemo; Castle Doom; Doctor Doom; Dáin Ironfoot; Goblin Cratermaker; Invisible Woman, Sue Storm; Iron Hills Blacksmith; Necklace of Girion; Robot Domination; … (4 more)
- **`inExile`** (15 cards) — An object in exile (wasCreatedByAction only covers this action's exile)
  - An Unexpected Party; Baron Helmut Zemo; Call Forth the Tempest; Doom Reigns Supreme; Gandalf, Goblins' Bane; Glamdring, Foe-hammer; Glóin the Mighty; Great Ugly-Looking Goblin; Gríma, Saruman's Footman; My Precious; Black Widow, Super Spy; … (4 more)
- **`attackingAlone`** (8 cards) — A creature attacking alone
  - Agent 13, Sharon Carter; Agents of S.H.I.E.L.D.; Bilbo's Ring; Black Widow, Double Agent; Crowd of True Believers; HYDRA Infiltration; Luke Cage, Power Man; S.H.I.E.L.D. Spy Kit
- **`powerAtMost`** (8 cards) — Power at most N (only powerAtLeast exists)
  - Dwarven Warriors; Eagle's Rescue; Elektra, Daughter of the Hand; Hulkling, Burgeoning Bruiser; Mentor of the Meek; Old Fat Spider; Raft Security Officer; Stern Scolding
- **`toughness`** (8 cards) — Toughness comparisons / bind toughness as a number
  - Arwen, Weaver of Hope; Baxter Building; I Am Iron Man; Last March of the Ents; Murdock's Crusade; Reptil, Dinomorpher; Stern Scolding; The Kingpin of Crime
- **`attached`** (7 cards) — Objects attached to a given object (inverse of hostOf)
  - Eagle's Rescue; Galadriel's Dismissal; Ronin, Shadow Stalker; Thorin, Mountain-king; Whiplash, Vengeful Engineer; Winter Soldier, Icy Assassin; Long-Lost Lances
- **`named`** (5 cards) — Objects with a given name
  - Castle Doom; Dáin Ironfoot; Iron Hills Blacksmith; Mole Man, Moloid Master; U.S.Agent, John Walker
- **`hasCounter`** (5 cards) — Objects with / without a given counter kind
  - Captain America, Super-Soldier; Dawn of a New Age; Great Ugly-Looking Goblin; Hellcat, Undying Vigilante; Kid Loki
- **`chosenType`** (3 cards) — Objects of the chosen creature type
  - An Unexpected Party; Orcrist, Goblin-cleaver; Raise the Palisade
- **`defendingPlayer`** (3 cards) — The defending player relative to an attacker
  - Captain America's Shield; Colossal Whale; Witch-king, Bringer of Ruin
- **`damagedThisTurn`** (2 cards) — Objects dealt damage this turn
  - Bitter Downfall; Red Guardian, Super-Soldier
- **`castFromZone`** (1 cards) — Zone a spell is cast from
  - Bilbo, Thief in the Night
- **`commander`** (1 cards) — The selected player's commander
  - Arcane Signet
- **`worthy`** (1 cards) — Worthy (Marvel)
  - Mjölnir, Hammer of Thor
- **`putFromBattlefieldThisTurn`** (1 cards) — Cards put into a graveyard from the battlefield this turn (Shape.diedThisTurn is Condition-only)
  - Supper for Spiders
- **`receivedCounterThisTurn`** (1 cards) — Objects you put +1/+1 counters on this turn
  - Kid Loki

### `Trigger`

- **`beginStep`** (27 cards) — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player
  - Absorbing Man; Alien Invasion; Avengers Assemble!; Beorn the Fierce; Bolg, Erebor's Reckoning; Chief Warg's Company; Dawn of a New Age; Doctor Doom; Gandalf, Party Guest; Glóin the Mighty; … (17 more)
- **`onceEachTurn`** (15 cards) — Limit a trigger to once each turn
  - Ant-Man, Colony Commander; Baron Helmut Zemo; Baron Strucker, HYDRA Overlord; Crossbones, Malicious Mercenary; Elrond, Moon-Reader; Knight of Wundagore; Kíli the Resourceful; Loki, God of Mischief; Moon Girl and Devil Dinosaur; Nimrodel Watcher; … (5 more)
- **`sagaChapter`** (14 cards) — When a lore counter is put / a (final) chapter ability resolves
  - Armor Wars; Avengers: Under Siege; Burn, Burn, Tree and Fern; Down in the Valley; Down, Down to Goblin-town; Old Fat Spider Can't See Me; Origin of the Avengers; Roads Go Ever, Ever On; Roll-Roll-Roll-Roll; The Coming of Galactus; … (4 more)
- **`leaveBattlefield`** (9 cards) — When the selected object leaves the battlefield
  - Banishing Light; Celebrate the Mountain-king; Cloak and Dagger, Entwined; Colossal Whale; Fiend Hunter; Roads Go Ever, Ever On; Secret Invasion; Super Villain Lockup; Web Up
- **`attackAlone`** (8 cards) — When the selected object attacks alone
  - Agent 13, Sharon Carter; Agents of S.H.I.E.L.D.; Bilbo's Ring; Black Widow, Double Agent; Crowd of True Believers; HYDRA Infiltration; Luke Cage, Power Man; S.H.I.E.L.D. Spy Kit
- **`becomeTarget`** (9 cards) — When the selected object becomes the target of a spell or ability
  - Dwarven Mattock; Falcon's Wing Harness; Gandalf, Wandering Wizard; Lake-town Mariners; Loki, God of Mischief; Old Fat Spider; Super Strength; Titania, Rugged Rumbler; Speedball, New Warrior
- **`becomeTapped`** (4 cards) — When the selected object becomes tapped (including tapped to pay a cost)
  - Agent Maria Hill; Captain America, Living Legend; Hawkeye's Bow; Hawkeye, Master Marksman
- **`dealtDamage`** (4 cards) — When the selected object is dealt damage (Enrage / watch-damage)
  - Red Hulk; The Black Arrow; The Incredible Hulk; The Sensational She-Hulk
- **`tokenEnters`** (4 cards) — When a token the player controls enters (enter + token selector may suffice if token creation exists)
  - Belladonna Took; Cavern-Hoard Dragon; Gleaming Splendor; Mister Fantastic, Reed Richards
- **`gainLife`** (3 cards) — Whenever the selected player gains life
  - Heroic Feast; Mirkwood Elk; Tigra, Feline Fury
- **`scry`** (3 cards) — Whenever the selected player scries
  - Celeborn the Wise; Nimrodel Watcher; Witch-king of Angmar
- **`theRingTemptsYou`** (2 cards) — Whenever the Ring tempts you / you choose a Ring-bearer
  - Sauron, the Dark Lord; Witch-king of Angmar
- **`wouldDraw`** (2 cards) — Would-draw replacement window (Trigger.draw is the actual event)
  - Bard, King of Dale; Plunder the Trollshaws
- **`whenYouDo`** (1 cards) — Nested delayed trigger after an optional action ('when you do')
  - Spider-Man, To the Rescue

### `Cost`

- **`tapPowerTotal`** (16 cards) — Tap creatures you control with total power N or more (Teamwork / Crew)
  - Atlantis Attacks; Cruel Alliance; Dependable Quinjet; Earth's Mightiest Heroes; Go Nuts!; Great Gilded Boat; HULK SMASH!; Helicarrier Strike; Murdock's Crusade; Repulsor Blast; … (6 more)
- **`wardNonmana`** (14 cards) — Nonmana ward payments
  - Captain America, Wings of Freedom; Cosmic Cube; Dwarven Mattock; Falcon's Wing Harness; Flowering of the White Tree; Gandalf, Wandering Wizard; Lake-town Mariners; Saruman of Many Colors; Sauron, the Dark Lord; Secret Invasion; … (4 more)
- **`manaX`** (8 cards) — Pay {X} / {X}{X} (ManaSymbol list has no X variable in Cost.mana as a bound value for later actions)
  - An Unexpected Party; Bruce Banner; Cavern-Hoard Dragon; Glamdring, Foe-hammer; Stature, Size Shifter; The Lord of the Eagles; The Scarlet Witch; Treasure Vault
- **`optionalAdditional`** (2 cards) — Optional additional cost (Kicker)
  - Galadriel's Dismissal; The Eagles Are Coming!
- **`tapArtifactsForGeneric`** (2 cards) — Tap artifacts to pay generic
  - Arc Reactor; Ironheart, Clever Champion
- **`life`** (1 cards) — Cost.life exists; combination with tap+addMana one-of is expressible if Condition/action compile
  - Mount Doom
- **`or`** (1 cards) — Cost.or exists; need discard-a-card (inHand) OR pay generic
  - Titania, Rugged Rumbler
- **`tapOther`** (1 cards) — Tap another matching permanent (not the tap symbol on the source)
  - The Shire

### `Condition`

- **`enteredThisTurn`** (29 cards) — This land entered this turn
  - Abomination, Terrifying Titan; Aerial Doombot; Bold Biochemist; Brave Brawler; Captain Marvel, Earth's Protector; Hercules, Prince of Power; Hulk, Gamma Goliath; Human Torch, Johnny Storm; Kang the Conqueror; Loki Laufeyson; … (19 more)
- **`sourceEnteredThisTurn`** (24 cards) — The source entered this turn
  - Abomination, Terrifying Titan; Aerial Doombot; Bold Biochemist; Brave Brawler; Captain Marvel, Earth's Protector; Hercules, Prince of Power; Hulk, Gamma Goliath; Human Torch, Johnny Storm; Kang the Conqueror; Loki Laufeyson; … (14 more)
- **`castWithTeamwork`** (12 cards) — This spell was cast using teamwork
  - Atlantis Attacks; Cruel Alliance; Earth's Mightiest Heroes; Go Nuts!; HULK SMASH!; Helicarrier Strike; Murdock's Crusade; Repulsor Blast; Team Tactics; Too Evil to Stay Dead; … (2 more)
- **`enduringStory`** (9 cards) — You have an enduring story (Storied is already a Keyword)
  - Balin, Loremaster; Bifur, Melodic Rider; Bombur, Gentle Dreamer; Dáin, Lord of the Iron Hills; Fíli the Pathfinder; Kíli the Resourceful; Ori, Keeper of Songs; Thorin Oakenshield; Óin the Brave
- **`not`** (7 cards) — Negation / unless (Condition has and, not or/not)
  - Chief Warg's Company; Minas Tirith; Olog-hai Crusher; Rivendell; The Black Gate; The Lonely Mountain; The Shire
- **`controlCount`** (5 cards) — Controller controls N or more matching objects
  - Alien Invasion; Ares, God of War; Chief Warg's Company; The Sentry, Golden Guardian; fogOnTheBarrowDowns
- **`countAtLeast`** (5 cards) — At least N objects match a selector (graveyard size, lore, quest counters, …)
  - Master's Councillors; Most Decrepit Old Bird; Punishing Punch; The Master of Lake-town; Tom Bombadil
- **`or`** (5 cards) — Activate only if this land entered this turn or you control a basic land
  - darkFortress; gatheringPlace; gleamingBastion; hiddenLair; trainingCompound
- **`any`** (2 cards) — any with a legendary-you-control selector is already expressible; listed only if other gaps remain
  - Haunt of the Dead Marshes; Rivendell
- **`firstThisTurn`** (2 cards) — The first matching event this turn
  - Bard's Company; Radagast of Rhosgobel
- **`kicked`** (2 cards) — This spell was kicked
  - Galadriel's Dismissal; The Eagles Are Coming!
- **`manaValueParity`** (2 cards) — Mana value is odd/even
  - Gollum, Riddle Master; Thanos, the Mad Titan
- **`attackedThisTurn`** (1 cards) — You attacked with N or more creatures this turn
  - Minas Tirith
- **`citysBlessing`** (1 cards) — You have the city's blessing
  - Andúril, Narsil Reforged
- **`resolvedThisTurnCount`** (1 cards) — This ability has resolved N times this turn
  - Belladonna Took
- **`modeNotChosenThisTurn`** (1 cards) — Choose a mode that hasn't been chosen this turn
  - The Vision

### `Ability`

- **`activatedOnce`** (24 cards) — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
  - Abomination, Terrifying Titan; Aerial Doombot; Bold Biochemist; Brave Brawler; Captain Marvel, Earth's Protector; Hercules, Prince of Power; Hulk, Gamma Goliath; Human Torch, Johnny Storm; Kang the Conqueror; Loki Laufeyson; … (14 more)
- **`keywordWard`** (14 cards) — Ward with a cost (mana, discard-a-type, sacrifice legendary, poison, pay-or-discard)
  - Captain America, Wings of Freedom; Cosmic Cube; Dwarven Mattock; Falcon's Wing Harness; Flowering of the White Tree; Gandalf, Wandering Wizard; Lake-town Mariners; Saruman of Many Colors; Sauron, the Dark Lord; Secret Invasion; … (4 more)
- **`keywordTeamwork`** (12 cards) — Teamwork N as an optional additional cost
  - Atlantis Attacks; Cruel Alliance; Earth's Mightiest Heroes; Go Nuts!; HULK SMASH!; Helicarrier Strike; Murdock's Crusade; Repulsor Blast; Team Tactics; Too Evil to Stay Dead; … (2 more)
- **`linkedExile`** (8 cards) — Paired exile-until-leaves (enter trigger + leave trigger sharing exiled objects)
  - Banishing Light; Celebrate the Mountain-king; Cloak and Dagger, Entwined; Colossal Whale; Fiend Hunter; Roads Go Ever, Ever On; Super Villain Lockup; Web Up
- **`activateFromZone`** (7 cards) — Activated ability that functions in the graveyard (or another non-battlefield zone)
  - Eagle's Rescue; Haunt of the Dead Marshes; Moment of Glory; Plunder the Trollshaws; Silvan Reveler; Tidings of War; Winter Soldier, Icy Assassin
- **`keywordCrew`** (4 cards) — Crew N
  - Dependable Quinjet; Great Gilded Boat; S.H.I.E.L.D. Flying Car; S.H.I.E.L.D. Helicarrier
- **`keywordFlashback`** (3 cards) — Flashback with a cost
  - Moment of Glory; Plunder the Trollshaws; Tidings of War
- **`keywordImprovise`** (2 cards) — Improvise
  - Arc Reactor; Ironheart, Clever Champion
- **`keywordKicker`** (2 cards) — Kicker
  - Galadriel's Dismissal; The Eagles Are Coming!
- **`gift`** (1 cards) — Gift (promise an opponent a token)
  - Bilbo's Gambit
- **`keywordAffinity`** (1 cards) — Affinity for a type/subtype
  - Cantankerous Keepers
- **`keywordBoast`** (1 cards) — Boast
  - Baron Helmut Zemo
- **`keywordCascade`** (1 cards) — Cascade
  - Call Forth the Tempest
- **`keywordExtort`** (1 cards) — Extort
  - The Kingpin of Crime
- **`keywordSneak`** (1 cards) — Sneak
  - Elektra, Daughter of the Hand

### `ContinuousEffect`

- **`setPowerToughness`** (14 cards) — Set base P/T to literal values (only from another object or a count exists)
  - Absorbing Man; Beorn the Fierce; Dependable Quinjet; Great Gilded Boat; I Am Iron Man; Iron Man Armor; Mirkwood Meditator; Moon Girl and Devil Dinosaur; Reptil, Dinomorpher; S.H.I.E.L.D. Helicarrier; … (4 more)
- **`setTypes`** (14 cards) — Set types/subtypes rather than only gain them
  - Absorbing Man; Beorn the Fierce; Dependable Quinjet; Great Gilded Boat; I Am Iron Man; Iron Man Armor; Mirkwood Meditator; Moon Girl and Devil Dinosaur; Reptil, Dinomorpher; S.H.I.E.L.D. Helicarrier; … (4 more)
- **`restrictManaSpend`** (12 cards) — Mana from an action may be spent only on matching events (current leftover is Elf-only)
  - Arcane Signet; Avengers Tower; Castle Doom; Delighted Halfling; Desolation of Smaug; Fíli and Kíli, Joyous; Hydraulic Helper; Mox Amber; Pelargir Survivor; Ronin, Shadow Stalker; … (2 more)
- **`addPowerToughnessPer`** (8 cards) — Pump / set PT from a count other than setPowerToughnessEqualToCount's lands-you-control leftover
  - Desert Were-Worm; Esgaroth Garrison; Iron Man, Master of Machines; Minas Tirith Garrison; Ms. Marvel, Kamala Khan; Namor the Sub-Mariner; Super-Adaptoid; Winter Soldier, Icy Assassin
- **`reduceCostByValue`** (8 cards) — Reduce cost by a computed value (flying power, opp artifacts, source power, gy count) — reduceCost only takes a literal Cost list
  - Call Forth the Tempest; Cavern-Hoard Dragon; Cosmic Cube; Glamdring; Loki Laufeyson; Part in Friendship; Punishing Punch; The Lord of the Eagles
- **`replace`** (7 cards) — replace already exists; need a would-die / would-go-to-gy trigger which putToGraveyard covers — exile-instead is expressible if replace actions can exile (compiler may not)
  - Bilbo, Thief in the Night; Grim Reaper, Lethal Legionnaire; Head of the Hunt; Pinecone Strike; Smite the Deathless; Thunderbolts Conspiracy; Winter Soldier, Icy Assassin
- **`canPlay`** (5 cards) — canPlay exists; need top-of-library + land/creature spell filters as a continuous permission
  - Call Forth the Tempest; Elven Chorus; Ka-Zar of the Savage Land; Part in Friendship; Tom Bombadil
- **`forbidAttack`** (5 cards) — Can't attack / attacks-if-able (forbid exists for Trigger; need an attack event plus a restriction combinator)
  - Alien Invasion; Ares, God of War; Chief Warg's Company; The Sentry, Golden Guardian; fogOnTheBarrowDowns
- **`extraTrigger`** (4 cards) — Matching triggered abilities trigger an additional time
  - Bifur, Melodic Rider; Chief of the Wilds; Wizard's Staff; Wonder Man, Hollywood Hero
- **`loseAbilities`** (4 cards) — Selected object loses all abilities
  - Frozen in Ice; Hellcat, Undying Vigilante; The Wondrous Wasp; enchantedRiverSGrasp
- **`mayLookAtTop`** (4 cards) — May look at the top card of the selected library any time
  - Daredevil, Man Without Fear; Elven Chorus; Iron Lad, Diverging Destiny; Ka-Zar of the Savage Land
- **`cantBeCountered`** (3 cards) — Selected spells can't be countered
  - Delighted Halfling; Gigantic Big Bear; Last March of the Ents
- **`forbidCast`** (3 cards) — Players matching a selector can't cast spells matching a selector
  - Bilbo's Gambit; Jennifer Walters; The Sensational She-Hulk
- **`skipsUntap`** (4 cards) — Selected permanents don't untap during the untap step
  - Bombur, Gentle Dreamer; Frozen in Ice; enchantedRiverSGrasp; Spider-Woman, Secret Agent
- **`cantBeBlockedBy`** (2 cards) — Can't be blocked by / if matching a selector (power at most/at least, tokens already exist as forbid block token this)
  - Bilbo, Unexpected Adventurer; Old Fat Spider
- **`cantBeBlockedExceptBy`** (2 cards) — Can't be blocked except by N or more creatures (menace is Keyword for N=2)
  - Troll of Khazad-dûm; Witch-king of Angmar
- **`gainAbility`** (2 cards) — gainAbility exists; granting a tap-add-mana activated ability to others needs Ability.activated as the granted ability (already in Ability) — compiler may not emit it
  - Elven Chorus; Thranduil the Strategist
- **`gainAbilityIf`** (3 cards) — Matching spells have flash / cost less with a 'first this turn' condition
  - Bard's Company; Radagast of Rhosgobel; Captain Mar-Vell, Space-Born
- **`handSize`** (2 cards) — Set / remove maximum hand size
  - Ms. Marvel, Kamala Khan; The Ten Rings
- **`modifyDamage`** (2 cards) — Replacement that changes how much damage is dealt
  - Hawkeye, Young Avenger; Mjölnir, Hammer of Thor
- **`preventDamage`** (2 cards) — Prevent (all) damage that would be dealt to/by a selector
  - Black Panther, Hope Enduring; Old Fat Spider Can't See Me
- **`replaceDraw`** (2 cards) — If you would draw (except the first in each draw step), draw N instead
  - Bard, King of Dale; Plunder the Trollshaws
- **`replaceTokenCreation`** (2 cards) — If you would create a Food, also create a Treasure
  - Bard, King of Dale; Bilbo, Fellow Conspirator
- **`copyActivatedAbilities`** (1 cards) — Gains the activated abilities of matching objects
  - Thranduil, the Elvenking
- **`reduceCost`** (1 cards) — reduceCost+if exists for tapped/attacking/died; missing damaged-this-turn shape
  - Bitter Downfall
- **`reduceCostIfCastFrom`** (1 cards) — Spells you cast from matching zones cost less
  - Bilbo, Thief in the Night
- **`reduceCostPer`** (1 cards) — Reduce cost by {1} per matching object
  - Cantankerous Keepers
- **`replaceEnterCounters`** (1 cards) — As matching objects enter, they enter with extra counters
  - Arwen, Weaver of Hope
- **`setSubtypes`** (1 cards) — Overwrite subtypes (gainSubtype only adds)
  - fogOnTheBarrowDowns
- **`reduceCostIfTargeting`** (1 cards) — Reduce costs of abilities you activate that target this object (reduceCost only this object's costs)
  - Dwarven Mauler
- **`gainSupertype`** (1 cards) — Gain a supertype in addition to other types (legendary)
  - Super-Soldier Serum
- **`forbidUntapWhileYouControl`** (1 cards) — Can't become untapped for as long as you control this
  - Spider-Woman, Secret Agent

### `CardAction`

- **`createToken`** (87 cards) — Create n tokens of a described kind
  - Agent 13, Sharon Carter; Agents of HYDRA; Alien Invasion; Andúril, Flame of the West; Ant-Man's Army; Ant-Man, Colony Commander; Aragorn, the Uniter; Arnim Zola, Bio-Fanatic; Avengers: Under Siege; Azog, Moria's Ruin; … (77 more)
- **`repeatN`** (22 cards) — Repeat an action / deal damage / draw / put counters X times where X is computed
  - Bolg of the North; Call Forth the Tempest; Cosmic Cube; Dáin of the Ancient Halls; Esgaroth Garrison; Glamdring; HULK SMASH!; Inside Information; Iron Fist, Living Weapon; Last March of the Ents; … (12 more)
- **`lookAt`** (21 cards) — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)
  - A.I.M. Synthoids; Avengers Tower; Boughside Wanderers; Colleen Wing, Street Samurai; Cosmic Cube; Daredevil, Man Without Fear; Dáin's Company; Elven Chorus; Falcon, Winged Wonder; Gandalf, Goblins' Bane; … (11 more)
- **`amass`** (17 cards) — Amass <subtype> N
  - Along the Crooked Way; Azog, Moria's Ruin; Bolg of the North; Bothersome Noisemaker; Down, Down to Goblin-town; Fearsome Goblin Pair; Gathering of Darkness; Goblin Plate Mail; Goblin-town Flunkies; Great Goblin, Foul-Hearted; … (7 more)
- **`mill`** (13 cards) — Target player mills N cards
  - Cantankerous Keepers; Glamdring, Foe-hammer; HYDRA Troopers; Master's Councillors; Mole Man, Moloid Master; Most Decrepit Old Bird; Palantír of Orthanc; Pelargir Survivor; Rapid Rescue; Rick Jones, Destined Sidekick; … (3 more)
- **`connive`** (11 cards) — Connive
  - A.I.M. Scientists; Baron Helmut Zemo; Baron Strucker, HYDRA Overlord; Kang, Temporal Tyrant; Leader, Super-Genius; M.O.D.O.K.; Madame Masque; Red Room Recruit; Swordsman, Sharp Scoundrel; Trickster's Stratagem; … (1 more)
- **`addManaPer`** (10 cards) — Add mana for each matching object
  - Armor Wars; Avengers: Under Siege; Bag End Banquet; Desert Were-Worm; Dragon's Desire; Elvish Archdruid; Roads Go Ever, Ever On; The Eagles Are Coming!; The Lonely Mountain; The Notary Hobbits
- **`chooseModes`** (11 cards) — Modal selection beyond exclusive chooseMode (one-or-both, choose-two-if, choose-both-if-teamwork)
  - Atlantis Attacks; Avengers Disassembled; Decoy Ploy; Epic Fight; Flame of Anor; Go Nuts!; HULK SMASH!; Murdock's Crusade; Pinecone Strike; Widow's Bite; The Vision
- **`randomize`** (10 cards) — Put on bottom in random order / pick a random card among
  - Boughside Wanderers; Call Forth the Tempest; Cosmic Cube; Dáin's Company; Getaway Barrel; Gríma, Saruman's Footman; Nick Fury, Agent of S.H.I.E.L.D.; Part in Friendship; Tom Bombadil; Tony Stark
- **`recruit`** (10 cards) — Recruit (draw, discard; if nonland discarded, create a Human Soldier)
  - Bard's Company; Celebrate the Mountain-king; Esgaroth Garrison; Great Gilded Boat; Lake-town Lookout; Long Lake Nuisance; Patient Instructor; Sound the Trumpets; The Mountain-king's Return; The Queen of Dale
- **`copy`** (9 cards) — Copy a permanent, spell, or ability
  - Absorbing Man; Echo, Perceptive Prodigy; Multiversal Incursion; Photon Blast Barrage; Scientist Supreme of A.I.M.; Secret Invasion; Shuri, Wakandan Inventor; Taskmaster, Mercenary Mimic; Ultron, Artificial Malevolence
- **`returnExiled`** (8 cards) — Return objects exiled by a linked action
  - Banishing Light; Celebrate the Mountain-king; Cloak and Dagger, Entwined; Colossal Whale; Fiend Hunter; Roads Go Ever, Ever On; Super Villain Lockup; Web Up
- **`eventAmount`** (8 cards) — Use the amount of damage/life/cards from the triggering event ('that much')
  - Bolg of the North; Hawkeye, Young Avenger; Red Hulk; The Black Arrow; The Incredible Hulk; The Kingpin of Crime; The Sensational She-Hulk; Ori, Plate Stacker
- **`removeCounter`** (6 cards) — Remove counters from the selected object
  - Arwen, Mortal Queen; Captain America, Super-Soldier; Dawn of a New Age; Mister Hyde, Monster Within; The Astonishing Ant-Man; enchantedRiverSGrasp
- **`transform`** (6 cards) — Transform this permanent
  - Bruce Banner; Jennifer Walters; King T'Challa; Monica Rambeau; Nick Fury, Agent of S.H.I.E.L.D.; Tony Stark
- **`exileThenReturn`** (5 cards) — Exile then return at a later trigger (end step / leaves)
  - Elrond, Moon-Reader; Roll-Roll-Roll-Roll; S.H.I.E.L.D. Flying Car; The Mind Stone; Wiccan, Rising Magician
- **`payThen`** (5 cards) — You may pay a cost. If you do, perform actions (resolution-time optional payment, not an activated cost)
  - Mentor of the Meek; Silvan Reveler; The Black Gate; The Kingpin of Crime; Ultron, Artificial Malevolence
- **`gainControl`** (4 cards) — Gain control of selected objects
  - Bilbo's Burglaring; Evil's Thrall; Sauron, the Lidless Eye; The Super Hero Civil War
- **`surveil`** (4 cards) — Surveil N
  - A.I.M. Synthoids; Falcon, Winged Wonder; Hour of Defeat; Surveillance Room
- **`addManaCombination`** (3 cards) — Add N mana in any combination of listed types / any color
  - Baxter Building; Desolation of Smaug; Relic of Sauron
- **`chooseCreatureType`** (3 cards) — Choose a creature type (as-enters or on resolution)
  - An Unexpected Party; Orcrist, Goblin-cleaver; Raise the Palisade
- **`chooseOddEven`** (2 cards) — Choose odd or even
  - Gollum, Riddle Master; Thanos, the Mad Titan
- **`extraCombat`** (2 cards) — An additional combat phase; typically with untap attackers
  - Desert Were-Worm; The Incredible Hulk
- **`investigate`** (2 cards) — Investigate / create a Clue
  - Agent 13, Sharon Carter; Panther Pounce
- **`theRingTemptsYou`** (2 cards) — The Ring tempts you
  - Sauron, the Dark Lord; Witch-king of Angmar
- **`behold`** (1 cards) — Behold a subtype
  - Elven Passage
- **`cascade`** (1 cards) — Exile until a cheaper nonland; you may cast it
  - Call Forth the Tempest
- **`becomeWithAbility`** (1 cards) — Lose other types, become Food artifacts, and gain a stated activated ability
  - Supper for Spiders
- **`exileUntil`** (1 cards) — Exile from the top until a matching card (nonland leftover)
  - Black Widow, Super Spy
- **`forEachCounterKind`** (1 cards) — For each kind of counter on a selected object, give another of that kind
  - Powerful Broker
- **`changeTargets`** (1 cards) — Choose new targets for another spell or ability
  - Speedball, New Warrior

### `TraditionalCardDefinition`

- **`tokenDescription`** (87 cards) — Inline token characteristics (or a TokenKind reference)
  - Agent 13, Sharon Carter; Agents of HYDRA; Alien Invasion; Andúril, Flame of the West; Ant-Man's Army; Ant-Man, Colony Commander; Aragorn, the Uniter; Arnim Zola, Bio-Fanatic; Avengers: Under Siege; Azog, Moria's Ruin; … (77 more)
- **`CardSubtype.Noble`** (25 cards) — CardPart.subtype uses CardSubtype; Noble has no constructor
  - Aragorn and Arwen, Wed; Aragorn, the Uniter; Arwen, Mortal Queen; Arwen, Weaver of Hope; Bard, King of Dale; Baron Helmut Zemo; Celeborn the Wise; Dáin of the Ancient Halls; Dáin, Lord of the Iron Hills; Elrond, Moon-Reader; … (15 more)
- **`sagaChapters`** (14 cards) — Printed Saga chapters (roman numeral + actions); CardPart has no chapter
  - Armor Wars; Avengers: Under Siege; Burn, Burn, Tree and Fern; Down in the Valley; Down, Down to Goblin-town; Old Fat Spider Can't See Me; Origin of the Avengers; Roads Go Ever, Ever On; Roll-Roll-Roll-Roll; The Coming of Galactus; … (4 more)
- **`CardSubtype.Mutant`** (10 cards) — CardPart.subtype uses CardSubtype; Mutant has no constructor
  - Beast, Erudite Aerialist; Justice, Vance Astrovik; Ms. Marvel, Kamala Khan; Namor the Sub-Mariner; Quicksilver, Brash Blur; Speed, Young Avenger; Storm, Windrider; The Scarlet Witch; Wiccan, Rising Magician; Wolverine, Fierce Fighter
- **`CardSubtype.Scientist`** (10 cards) — CardPart.subtype uses CardSubtype; Scientist has no constructor
  - A.I.M. Scientists; Arnim Zola, Bio-Fanatic; Beast, Erudite Aerialist; Bold Biochemist; Bruce Banner; Doctor Doom; Leader, Super-Genius; Mister Fantastic, Reed Richards; Scientist Supreme of A.I.M.; The Astonishing Ant-Man
- **`CardSubtype.Gamma`** (8 cards) — CardPart.subtype uses CardSubtype; Gamma has no constructor
  - Abomination, Terrifying Titan; Doc Samson, Super Psychiatrist; Hulk, Gamma Goliath; Leader, Super-Genius; Red Hulk; She-Hulk, Jade Defender; The Incredible Hulk; The Sensational She-Hulk
- **`CardSubtype.Plan`** (8 cards) — CardPart.subtype uses CardSubtype; Plan has no constructor
  - Claim the Kingdom; Construct a Cosmic Cube; Death to Our Enemies; Doom Reigns Supreme; Political Triumph; Rewrite History; Robot Domination; The Masters of Evil
- **`entersTappedUnless`** (7 cards) — Enters tapped unless a condition (replace-enter is only compiled for always-tapped)
  - Chief Warg's Company; Minas Tirith; Olog-hai Crusher; Rivendell; The Black Gate; The Lonely Mountain; The Shire
- **`CardSubtype.Saga`** (6 cards) — CardPart.subtype uses CardSubtype; Saga has no constructor
  - Armor Wars; Avengers: Under Siege; Origin of the Avengers; The Coming of Galactus; The Super Hero Civil War; World War Hulk
- **`otherFace`** (6 cards) — Second face of a transforming DFC (CardPart.alternative is Adventure-only)
  - Bruce Banner; Jennifer Walters; King T'Challa; Monica Rambeau; Nick Fury, Agent of S.H.I.E.L.D.; Tony Stark
- **`CardSubtype.Artificer`** (5 cards) — CardPart.subtype uses CardSubtype; Artificer has no constructor
  - Iron Hills Blacksmith; Lake-town Toymaker; Shuri, Wakandan Inventor; Tony Stark; Whiplash, Vengeful Engineer
- **`CardSubtype.Berserker`** (5 cards) — CardPart.subtype uses CardSubtype; Berserker has no constructor
  - Hulk, Gamma Goliath; Red Hulk; Roxxon Brutes; The Incredible Hulk; Wolverine, Fierce Fighter
- **`CardSubtype.Cat`** (3 cards) — CardPart.subtype uses CardSubtype; Cat has no constructor
  - Knight of Wundagore; Pet Avengers; Tigra, Feline Fury
- **`CardSubtype.Doctor`** (3 cards) — CardPart.subtype uses CardSubtype; Doctor has no constructor
  - Doc Samson, Super Psychiatrist; Moonstone, Harsh Mistress; Night Nurse, Healer of Heroes
- **`CardSubtype.Mercenary`** (3 cards) — CardPart.subtype uses CardSubtype; Mercenary has no constructor
  - Crossbones, Malicious Mercenary; Killmonger, Scourge of Wakanda; Taskmaster, Mercenary Mimic
- **`CardSubtype.Skrull`** (3 cards) — CardPart.subtype uses CardSubtype; Skrull has no constructor
  - Hulkling, Burgeoning Bruiser; Super-Skrull; Undercover Skrull
- **`CardSubtype.Troll`** (3 cards) — CardPart.subtype uses CardSubtype; Troll has no constructor
  - Olog-hai Crusher; Tom, Bert, and William; Troll of Khazad-dûm
- **`asEntersChoice`** (3 cards) — As-this-enters replacement/choice on the face
  - An Unexpected Party; Orcrist, Goblin-cleaver; Raise the Palisade
- **`entersWithCounters`** (3 cards) — Enters with shield counters
  - Arwen, Mortal Queen; Captain America, Super-Soldier; Dawn of a New Age
- **`CardSubtype.Arcane`** (2 cards) — CardPart.subtype uses CardSubtype; Arcane has no constructor
  - Hex Magic; We Say Thee Nay!
- **`CardSubtype.Assassin`** (2 cards) — CardPart.subtype uses CardSubtype; Assassin has no constructor
  - Bullseye, Death Dealer; Winter Soldier, Icy Assassin
- **`CardSubtype.Detective`** (2 cards) — CardPart.subtype uses CardSubtype; Detective has no constructor
  - Jessica Jones, Private Eye; Misty Knight, Hero for Hire
- **`CardSubtype.Dog`** (2 cards) — CardPart.subtype uses CardSubtype; Dog has no constructor
  - Long-Bodied Grey Dog; Pet Avengers
- **`CardSubtype.Inhuman`** (2 cards) — CardPart.subtype uses CardSubtype; Inhuman has no constructor
  - Ms. Marvel, Kamala Khan; Quake, Agent of S.H.I.E.L.D.
- **`CardSubtype.Ninja`** (2 cards) — CardPart.subtype uses CardSubtype; Ninja has no constructor
  - Elektra, Daughter of the Hand; Ninja of the Hand
- **`CardSubtype.Peasant`** (2 cards) — CardPart.subtype uses CardSubtype; Peasant has no constructor
  - Pelargir Survivor; The Gaffer
- **`CardSubtype.Snake`** (2 cards) — CardPart.subtype uses CardSubtype; Snake has no constructor
  - Serpent Specialist; The Serpent Society
- **`CardSubtype.Sorcerer`** (2 cards) — CardPart.subtype uses CardSubtype; Sorcerer has no constructor
  - Loki Laufeyson; Loki, God of Mischief
- **`CardSubtype.Warlock`** (2 cards) — CardPart.subtype uses CardSubtype; Warlock has no constructor
  - The Scarlet Witch; Wiccan, Rising Magician
- **`CardSubtype.Wraith`** (2 cards) — CardPart.subtype uses CardSubtype; Wraith has no constructor
  - Witch-king of Angmar; Witch-king, Bringer of Ruin
- **`CardSubtype.Alien`** (1 cards) — CardPart.subtype uses CardSubtype; Alien has no constructor
  - Fin Fang Foom
- **`CardSubtype.Ape`** (1 cards) — CardPart.subtype uses CardSubtype; Ape has no constructor
  - Guerrilla Gorilla
- **`CardSubtype.Barbarian`** (1 cards) — CardPart.subtype uses CardSubtype; Barbarian has no constructor
  - Ka-Zar of the Savage Land
- **`CardSubtype.Demigod`** (1 cards) — CardPart.subtype uses CardSubtype; Demigod has no constructor
  - Hercules, Prince of Power
- **`CardSubtype.Elk`** (1 cards) — CardPart.subtype uses CardSubtype; Elk has no constructor
  - Mirkwood Elk
- **`CardSubtype.Eternal`** (1 cards) — CardPart.subtype uses CardSubtype; Eternal has no constructor
  - Thanos, the Mad Titan
- **`CardSubtype.Frog`** (1 cards) — CardPart.subtype uses CardSubtype; Frog has no constructor
  - Pet Avengers
- **`CardSubtype.Gate`** (1 cards) — CardPart.subtype uses CardSubtype; Gate has no constructor
  - The Black Gate
- **`CardSubtype.Horse`** (1 cards) — CardPart.subtype uses CardSubtype; Horse has no constructor
  - Troop of Ponies
- **`CardSubtype.Infinity`** (1 cards) — CardPart.subtype uses CardSubtype; Infinity has no constructor
  - The Mind Stone
- **`CardSubtype.Nightmare`** (1 cards) — CardPart.subtype uses CardSubtype; Nightmare has no constructor
  - Haunt of the Dead Marshes
- **`CardSubtype.Performer`** (1 cards) — CardPart.subtype uses CardSubtype; Performer has no constructor
  - Wonder Man, Hollywood Hero
- **`CardSubtype.Rabbit`** (1 cards) — CardPart.subtype uses CardSubtype; Rabbit has no constructor
  - Nasty Little Rabbit
- **`CardSubtype.Samurai`** (1 cards) — CardPart.subtype uses CardSubtype; Samurai has no constructor
  - Colleen Wing, Street Samurai
- **`CardSubtype.Squirrel`** (1 cards) — CardPart.subtype uses CardSubtype; Squirrel has no constructor
  - The Unbeatable Squirrel Girl
- **`CardSubtype.Stone`** (1 cards) — CardPart.subtype uses CardSubtype; Stone has no constructor
  - The Mind Stone
- **`CardSubtype.Vampire`** (1 cards) — CardPart.subtype uses CardSubtype; Vampire has no constructor
  - Unliving Legionnaire
- **`CardSubtype.Whale`** (1 cards) — CardPart.subtype uses CardSubtype; Whale has no constructor
  - Colossal Whale

### `CounterKind`

`CounterKind` is used by `CardAction.putCounter`. It currently has only `plusOnePlusOne`.

- **`lore`** (14 cards) — Lore counters (putCounter only has plusOnePlusOne; CounterKind is used by CardAction)
  - Armor Wars; Avengers: Under Siege; Burn, Burn, Tree and Fern; Down in the Valley; Down, Down to Goblin-town; Old Fat Spider Can't See Me; Origin of the Avengers; Roads Go Ever, Ever On; Roll-Roll-Roll-Roll; The Coming of Galactus; … (4 more)
- **`named`** (10 cards) — Named counters other than +1/+1 (hone, trample, quest, shadow, finality, …)
  - Beorn the Fierce; Dwalin, Weaponmaster; Grim Reaper, Lethal Legionnaire; Jessica Jones, Private Eye; Last Light of Durin's Day; Minas Morgul, Dark Fortress; Quicksilver, Brash Blur; Sting, Bilbo's Sword; Thunderbolts Conspiracy; Winter Soldier, Icy Assassin
- **`Hope`** (1 cards) — Named counter kind beyond +1/+1
  - Dawn of a New Age
- **`IndestructibleCounter`** (1 cards) — Named counter kind beyond +1/+1
  - Arwen, Mortal Queen
- **`Shield`** (1 cards) — Named counter kind beyond +1/+1
  - Captain America, Super-Soldier

## Cards with no tagged type gap

The first pass listed 44 remaining cards that did not match a missing-constructor
pattern. Conversion against `toCardDef` split them:

### Converted to `TraditionalCardDefinition`

These 30 cards now compile through leftovers onto the same modeled `CardDef`
(Oracle still matches). Catalog files: `Hobbit.lean`, `HobbitEternal.lean`,
`MarvelSuperHeroes.lean`.

**Hobbit (9):** Bard the Bowman, Bolg's Company, Elven Raft-Steerer, Iron Hills
Stalwart, Mirkwood Nurturer, Old Thrush, The Chief Warg, Wargling, Wilderland
Scrounger.

**Hobbit Eternal (2):** Esquire of the King, Gandalf, Shadow's Foe.

**Marvel Super Heroes (19):** Agent Phil Coulson, Attuma, Atlantean Warlord,
Blazing Crescendo, Call Damage Control, Giant-Sized Flying Ant, HYDRA Assault
Robot, Hero in Training, K'un-Lun Warrior, Mockingbird, Ace Agent, Photon,
Living Light, Pym Particles, Restorative Technique, The Mighty Thor, Jane
Foster, The Thing, Ben Grimm, Thirst for Knowledge, Vision of Love, Wakandan
Royal Guard, White Widow, Free Agent, Yellowjacket, Heartless Marauder.

Leftovers added in `Definition.lean` include ferocious attack shapes, landfall
tap/untap, attach-target-equipment, second-draw +1/+1/lifelink, haste-if-other-
subtype, sacrifice-another-subtype mana, grant-vigilance-unblockable,
pump-then-exile-top, choose-mode ETB, you-cast-noncreature +1/+1 each other,
another-Villain pump/lifelink, plus-one-on-each-other-subtype, Merfolk attack
draw, legendary-creature activated cost reduction, and the enter/search/modal
spell leftovers those printings need.

### Cards that still cannot convert

Closer reading of the remaining 14 found constructor gaps. They stay in the
catalog as `CardDef` helpers. Evidence is the printed ability vs the current
inductives (not a missing leftover for an expressible spelling).

- **Dwarven Mauler** — Equip abilities you activate that target this creature
  cost {2} less. `ContinuousEffect.reduceCost` only reduces *this object's*
  costs. There is no selector for “equip abilities you activate that target
  this.”
- **Supper for Spiders** — Put onto the battlefield all creature cards in
  opponents' graveyards that were put there *from the battlefield this turn*;
  they become Food artifacts with an activated ability. `Shape.diedThisTurn`
  is only set from a `Condition`, not a selector conjunct, and there is no
  `CardAction` to change types to Food and grant an ability.
- **Long-Lost Lances** — During your turn, *creatures you control that are
  equipped* have first strike and vigilance. That needs `Selector.attached`
  (inverse of `hostOf`). Equipped-creature host bonuses already exist; this
  static is the other direction.
- **Ori, Plate Stacker** — Destroy all artifacts and enchantments opponents
  control; gain 1 life *for each permanent destroyed this way*.
  `CardAction.gainLife` takes a literal `Nat`; `CardAction.eventAmount` /
  `Selector.countOf` / `Range.computed` are missing.
- **Black Widow, Super Spy** — Combat-damage exile from the top until a
  nonland, then an optional +1/+1 or cast-the-exiled-card. Needs
  `Selector.topNOfLibrary` / exile-until and `Selector.inExile` for the
  leftover nonland.
- **Captain Mar-Vell, Space-Born** — As long as an opponent has cast a spell
  this turn, you may cast spells as though they had flash.
  `ContinuousEffect.gainAbilityIf` / “as though they had flash” is missing
  (`Condition.happened` on an opponent's `castSpell` exists, but granting
  flash to spells you cast does not).
- **Kid Loki** — Each creature you control that you've put +1/+1 counters on
  *this turn* has hexproof. `Selector.hasCounter` and a “this turn” put-
  counters window are missing. (The second-card +1/+1 on self is already
  leftover-expressible as `onDrawSecondPlusOne`, but the static is not.)
- **Powerful Broker** — For each *kind of counter* on target permanent or
  player, give another counter of that kind. No constructor iterates counter
  kinds.
- **Speedball, New Warrior** — Whenever a player casts a spell that targets
  Speedball, pump and *choose new targets for that spell*. `Trigger.becomeTarget`
  is missing (also listed for other cards); changing targets of another spell
  is not a `CardAction`.
- **Spider-Man, To the Rescue** — You may tap him. *When you do*, another
  target nonattacking creature gains indestructible. Nested “when you do”
  delayed trigger is not a `Trigger` constructor.
- **Spider-Woman, Secret Agent** — Tap target opponent creature; it can't
  become untapped for as long as you control Spider-Woman.
  `ContinuousEffect.skipsUntap` / “can't become untapped while you control
  this” is missing.
- **Super-Soldier Serum** — Enchanted creature is a *legendary Soldier* in
  addition to its other types, and attach *any number* of Equipment you
  control. No `ContinuousEffect.gainSupertype`; `Range.anyNumber` is missing
  (only finite `range lo hi`).
- **The Masters of Evil** — Search your library for a *Plan* card.
  `CardSubtype.plan` does not exist (`CardPart.subtype` / `Selector.subtype`
  can't name it). Other Villains +2/+1 is already expressible.
- **The Vision** — Choose one *that hasn't been chosen this turn*.
  `Condition.firstThisTurn` / “mode not chosen this turn” is missing.
  `CardAction.chooseMode` has no per-mode-this-turn exclusion.

## Adjacent inductives

These are not in the requested list but block a conversion of the listed types:

| Inductive | Used by | Missing constructors that remaining cards need |
| --- | --- | --- |
| `CardSubtype` | `CardPart.subtype`, `Selector.subtype` | Noble, Scientist, Mutant, Gamma, Plan, Saga, Artificer, Berserker, Troll, Mercenary, Doctor, Skrull, Cat, and others listed per card as `TraditionalCardDefinition.CardSubtype.*` |
| `Keyword` | `Ability.keyword` | Ward, Crew, Kicker, Flashback, Cascade, Affinity, Teamwork, Improvise, Extort, Sneak, Boast, Daybound/Nightbound (some of these may instead be spelled as `Ability`/`ContinuousEffect` without a `Keyword` constructor) |
| `CounterKind` | `CardAction.putCounter` | lore, shield, hope, hone, trample, quest, shadow, finality, indestructible, and other named counters |

`CardPart` also has no `loyalty`, `colorIndicator`, `chapter`, or DFC-back
face (`alternative` is the Adventure face). Those are listed under
`TraditionalCardDefinition`.

## Per-card index

Every remaining supported catalog card. Constructors are `Type.ctor`.
Converted cards from the previous untagged set are omitted here.

### The Hobbit (HOB) (117 cards)

**Along the Crooked Way** (`alongTheCrookedWay`)

- `CardAction.amass` — Amass <subtype> N

**An Unexpected Party** (`anUnexpectedParty`)

- `CardAction.chooseCreatureType` — Choose a creature type (as-enters or on resolution)
- `Selector.chosenType` — Objects of the chosen creature type
- `TraditionalCardDefinition.asEntersChoice` — As-this-enters replacement/choice on the face
- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.inExile` — An object in exile (wasCreatedByAction only covers this action's exile)
- `Cost.manaX` — Pay {X} / {X}{X} (ManaSymbol list has no X variable in Cost.mana as a bound value for later actions)

**Azog, Moria's Ruin** (`azogMoriaSRuin`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.army` — Army (CardSubtype.army is also missing; used via Selector.subtype)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.amass` — Amass <subtype> N

**Balin, Loremaster** (`balinLoremaster`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Condition.enduringStory` — You have an enduring story (Storied is already a Keyword)
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)


**Bard's Company** (`bardsCompany`)

- `ContinuousEffect.gainAbilityIf` — Matching spells have flash / cost less with a 'first this turn' condition
- `Condition.firstThisTurn` — The first matching event this turn
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.recruit` — Recruit (draw, discard; if nonland discarded, create a Human Soldier)

**Bard, King of Dale** (`bardKingOfDale`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `ContinuousEffect.replaceDraw` — If you would draw (except the first in each draw step), draw N instead
- `Trigger.wouldDraw` — Would-draw replacement window (Trigger.draw is the actual event)
- `ContinuousEffect.replaceTokenCreation` — If tokens would be created, create twice as many instead
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Bejeweled Warg** (`bejeweledWarg`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Belladonna Took** (`belladonnaTook`)

- `Condition.resolvedThisTurnCount` — This ability has resolved N times this turn
- `Trigger.tokenEnters` — When a token the player controls enters (enter + token selector may suffice if token creation exists)

**Beorn the Fierce** (`beornTheFierce`)

- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player
- `ContinuousEffect.setPowerToughness` — Set base P/T to literal values (only from another object or a count exists)
- `ContinuousEffect.setTypes` — Set types/subtypes rather than only gain them
- `CounterKind.named` — Named counters other than +1/+1 (hone, trample, quest, shadow, finality, …)

**Bifur, Melodic Rider** (`bifurMelodicRider`)

- `Condition.enduringStory` — You have an enduring story (Storied is already a Keyword)
- `ContinuousEffect.extraTrigger` — Matching triggered abilities trigger an additional time

**Bilbo's Gambit** (`bilboSGambit`)

- `Ability.gift` — Gift (promise an opponent a token)
- `ContinuousEffect.forbidCast` — Players matching a selector can't cast spells matching a selector
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Bilbo, Thief in the Night** (`bilboThiefInTheNight`)

- `Selector.castFromZone` — Zone a spell is cast from
- `ContinuousEffect.replace` — replace already exists; need a would-die / would-go-to-gy trigger which putToGraveyard covers — exile-instead is expressible if replace actions can exile (compiler may not)
- `ContinuousEffect.reduceCostIfCastFrom` — Spells you cast from matching zones cost less

**Bolg of the North** (`bolgOfTheNorth`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.army` — Army (CardSubtype.army is also missing; used via Selector.subtype)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.amass` — Amass <subtype> N
- `CardAction.eventAmount` — Bind/use an amount from a previous action or trigger (that much, excess, sacrificed power)
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `Selector.countOf` — Numeric value derived from a count or characteristic


**Bombur, Gentle Dreamer** (`bomburGentleDreamer`)

- `Condition.enduringStory` — You have an enduring story (Storied is already a Keyword)
- `ContinuousEffect.skipsUntap` — Selected permanents don't untap during the untap step

**Bothersome Noisemaker** (`bothersomeNoisemaker`)

- `Selector.army` — Army (CardSubtype.army is also missing; used via Selector.subtype)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.amass` — Amass <subtype> N

**Boughside Wanderers** (`boughsideWanderers`)

- `SetPredicate.distinctNames` — Set-wide name constraints
- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)
- `CardAction.randomize` — Put on bottom in random order / pick a random card among

**Burn, Burn, Tree and Fern** (`burnBurnTreeAndFern`)

- `TraditionalCardDefinition.sagaChapters` — Printed Saga chapters (roman numeral + actions); CardPart has no chapter
- `Trigger.sagaChapter` — When a lore counter is put / a (final) chapter ability resolves
- `CounterKind.lore` — Lore counters (putCounter only has plusOnePlusOne; CounterKind is used by CardAction)

**Cantankerous Keepers** (`cantankerousKeepers`)

- `SetPredicate.distinctNames` — Set-wide name constraints
- `Ability.keywordAffinity` — Affinity for a type/subtype
- `ContinuousEffect.reduceCostPer` — Reduce cost by {1} per matching object
- `CardAction.mill` — Target player mills N cards

**Celebrate the Mountain-king** (`celebrateTheMountainKing`)

- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield
- `Ability.linkedExile` — Paired exile-until-leaves (enter trigger + leave trigger sharing exiled objects)
- `CardAction.returnExiled` — Return objects exiled by a linked action
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.recruit` — Recruit (draw, discard; if nonland discarded, create a Human Soldier)
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)

**Chief Warg's Company** (`chiefWargsCompany`)

- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player
- `Condition.not` — Negation / unless (Condition has and, not or/not)
- `TraditionalCardDefinition.entersTappedUnless` — Enters tapped unless a condition (replace-enter is only compiled for always-tapped)
- `ContinuousEffect.forbidAttack` — Can't attack / attacks-if-able (forbid exists for Trigger; need an attack event plus a restriction combinator)
- `Condition.controlCount` — Controller controls N or more matching objects
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Dancing from Dark to Dawn** (`dancingFromDarkToDawn`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.manaValue` — Mana-value comparisons
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Desert Were-Worm** (`desertWereWorm`)

- `ContinuousEffect.addPowerToughnessPer` — Pump / set PT from a count other than setPowerToughnessEqualToCount's lands-you-control leftover
- `Selector.countOf` — Numeric value derived from a count or characteristic
- `CardAction.extraCombat` — An additional combat phase; typically with untap attackers
- `CardAction.addManaPer` — Add mana for each matching object

**Desolation of Smaug** (`desolationOfSmaug`)

- `CardAction.addManaCombination` — Add N mana in any combination of listed types / any color
- `ContinuousEffect.restrictManaSpend` — Mana from an action may be spent only on matching events (current leftover is Elf-only)

**Dori, Bearer of Friends** (`doriBearerOfFriends`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Down in the Valley** (`downInTheValley`)

- `TraditionalCardDefinition.sagaChapters` — Printed Saga chapters (roman numeral + actions); CardPart has no chapter
- `Trigger.sagaChapter` — When a lore counter is put / a (final) chapter ability resolves
- `CounterKind.lore` — Lore counters (putCounter only has plusOnePlusOne; CounterKind is used by CardAction)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Down, Down to Goblin-town** (`downDownToGoblinTown`)

- `TraditionalCardDefinition.sagaChapters` — Printed Saga chapters (roman numeral + actions); CardPart has no chapter
- `Trigger.sagaChapter` — When a lore counter is put / a (final) chapter ability resolves
- `CounterKind.lore` — Lore counters (putCounter only has plusOnePlusOne; CounterKind is used by CardAction)
- `Selector.army` — Army (CardSubtype.army is also missing; used via Selector.subtype)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.amass` — Amass <subtype> N

**Dwalin, Weaponmaster** (`dwalinWeaponmaster`)

- `CounterKind.named` — Named counters other than +1/+1 (hone, trample, quest, shadow, finality, …)

**Dwarven Mattock** (`dwarvenMattock`)

- `Trigger.becomeTarget` — When the selected object becomes the target of a spell or ability
- `Ability.keywordWard` — Ward with a cost (mana, discard-a-type, sacrifice legendary, poison, pay-or-discard)
- `Cost.wardNonmana` — Nonmana ward payments

**Dwarven Mauler** (`dwarvenMauler`)

- `ContinuousEffect.reduceCostIfTargeting` — Reduce costs of abilities you activate that target this object (reduceCost only this object's costs)


**Dwarven Shortsword** (`dwarvenShortsword`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Dáin Ironfoot** (`dainIronfoot`)

- `Selector.color` — Objects of a color / colorless
- `Selector.named` — Objects with a given name
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Dáin's Company** (`dainsCompany`)

- `SetPredicate.distinctNames` — Set-wide name constraints
- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)
- `CardAction.randomize` — Put on bottom in random order / pick a random card among

**Dáin, Lord of the Iron Hills** (`dainLordOfTheIronHills`)

- `Condition.enduringStory` — You have an enduring story (Storied is already a Keyword)
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Eagle's Rescue** (`eaglesRescue`)

- `Selector.powerAtMost` — Power at most N (only powerAtLeast exists)
- `Selector.attached` — Objects attached to a given object (inverse of hostOf)
- `Ability.activateFromZone` — Activated ability that functions in the graveyard (or another non-battlefield zone)

**Elrond, Moon-Reader** (`elrondMoonReader`)

- `Trigger.onceEachTurn` — Limit a trigger to once each turn
- `CardAction.exileThenReturn` — Exile then return at a later trigger (end step / leaves)
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Elven Passage** (`elvenPassage`)

- `Selector.inHand` — An object in a hand
- `CardAction.behold` — Behold a subtype


**Esgaroth Garrison** (`esgarothGarrison`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `ContinuousEffect.addPowerToughnessPer` — Pump / set PT from a count other than setPowerToughnessEqualToCount's lands-you-control leftover
- `Selector.countOf` — Numeric value derived from a count or characteristic
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.recruit` — Recruit (draw, discard; if nonland discarded, create a Human Soldier)
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed

**Fearsome Goblin Pair** (`fearsomeGoblinPair`)

- `Selector.army` — Army (CardSubtype.army is also missing; used via Selector.subtype)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.amass` — Amass <subtype> N

**Fíli the Pathfinder** (`filiThePathfinder`)

- `Condition.enduringStory` — You have an enduring story (Storied is already a Keyword)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Gandalf, Goblins' Bane** (`gandalfGoblinsBane`)

- `Selector.inExile` — An object in exile (wasCreatedByAction only covers this action's exile)
- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)

**Gandalf, Wandering Wizard** (`gandalfWanderingWizard`)

- `Trigger.becomeTarget` — When the selected object becomes the target of a spell or ability
- `Ability.keywordWard` — Ward with a cost (mana, discard-a-type, sacrifice legendary, poison, pay-or-discard)
- `Cost.wardNonmana` — Nonmana ward payments

**Gathering of Darkness** (`gatheringOfDarkness`)

- `Selector.army` — Army (CardSubtype.army is also missing; used via Selector.subtype)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.amass` — Amass <subtype> N

**Getaway Barrel** (`getawayBarrel`)

- `SetPredicate.distinctNames` — Set-wide name constraints
- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CardAction.randomize` — Put on bottom in random order / pick a random card among

**Gigantic Big Bear** (`giganticBigBear`)

- `ContinuousEffect.cantBeCountered` — Selected spells can't be countered

**Glamdring, Foe-hammer** (`glamdringFoeHammer`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `SetPredicate.distinctNames` — Set-wide name constraints
- `Selector.inExile` — An object in exile (wasCreatedByAction only covers this action's exile)
- `Cost.manaX` — Pay {X} / {X}{X} (ManaSymbol list has no X variable in Cost.mana as a bound value for later actions)
- `CardAction.mill` — Target player mills N cards

**Gleaming Splendor** (`gleamingSplendor`)

- `Trigger.tokenEnters` — When a token the player controls enters (enter + token selector may suffice if token creation exists)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Glóin the Mighty** (`gloinTheMighty`)

- `Selector.inExile` — An object in exile (wasCreatedByAction only covers this action's exile)
- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player

**Goblin Plate Mail** (`goblinPlateMail`)

- `Selector.army` — Army (CardSubtype.army is also missing; used via Selector.subtype)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.amass` — Amass <subtype> N

**Goblin-town Flunkies** (`goblinTownFlunkies`)

- `Selector.army` — Army (CardSubtype.army is also missing; used via Selector.subtype)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.amass` — Amass <subtype> N

**Gollum, Riddle Master** (`gollumRiddleMaster`)

- `CardAction.chooseOddEven` — Choose odd or even
- `Condition.manaValueParity` — Mana value is odd/even
- `Selector.manaValue` — Mana-value comparisons
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)

**Great Gilded Boat** (`greatGildedBoat`)

- `Cost.tapPowerTotal` — Tap creatures with total power N or more
- `Ability.keywordCrew` — Crew N
- `Selector.inHand` — A card in hand for Cost.discard
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.recruit` — Recruit (draw, discard; if nonland discarded, create a Human Soldier)
- `ContinuousEffect.setPowerToughness` — Set base P/T to literal values (only from another object or a count exists)
- `ContinuousEffect.setTypes` — Set types/subtypes rather than only gain them

**Great Ugly-Looking Goblin** (`greatUglyLookingGoblin`)

- `Selector.inExile` — An object in exile (wasCreatedByAction only covers this action's exile)
- `Selector.hasCounter` — Objects with / without a given counter kind
- `CardAction.amass` — Amass <subtype> N

**Head of the Hunt** (`headOfTheHunt`)

- `ContinuousEffect.replace` — replace already exists; need a would-die / would-go-to-gy trigger which putToGraveyard covers — exile-instead is expressible if replace actions can exile (compiler may not)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Inside Information** (`insideInformation`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.manaValue` — Mana-value comparisons
- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `Selector.countOf` — Numeric value derived from a count or characteristic

**Iron Hills Blacksmith** (`ironHillsBlacksmith`)

- `Selector.color` — Objects of a color / colorless
- `Selector.named` — Objects with a given name
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `TraditionalCardDefinition.CardSubtype.Artificer` — CardPart.subtype uses CardSubtype; Artificer has no constructor


**Key to the Side-Door** (`keyToTheSideDoor`)

- `SetPredicate.shareName` — The selected objects share a name

**Kíli the Resourceful** (`kiliTheResourceful`)

- `Trigger.onceEachTurn` — Limit a trigger to once each turn
- `Condition.enduringStory` — You have an enduring story (Storied is already a Keyword)

**Lake-town Lookout** (`laketownLookout`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.recruit` — Recruit (draw, discard; if nonland discarded, create a Human Soldier)

**Lake-town Mariners** (`lakeTownMariners`)

- `Trigger.becomeTarget` — When the selected object becomes the target of a spell or ability
- `Ability.keywordWard` — Ward with a cost (mana, discard-a-type, sacrifice legendary, poison, pay-or-discard)
- `Cost.wardNonmana` — Nonmana ward payments

**Lake-town Toymaker** (`lakeTownToymaker`)

- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player
- `TraditionalCardDefinition.CardSubtype.Artificer` — CardPart.subtype uses CardSubtype; Artificer has no constructor

**Last Light of Durin's Day** (`lastLightOfDurinSDay`)

- `CounterKind.named` — Named counters other than +1/+1 (hone, trample, quest, shadow, finality, …)

**Long Lake Nuisance** (`longLakeNuisance`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.recruit` — Recruit (draw, discard; if nonland discarded, create a Human Soldier)

**Long-Bodied Grey Dog** (`longBodiedGreyDog`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `TraditionalCardDefinition.CardSubtype.Dog` — CardPart.subtype uses CardSubtype; Dog has no constructor

**Master's Councillors** (`masterSCouncillors`)

- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `Condition.countAtLeast` — At least N objects match a selector (graveyard size, lore, quest counters, …)
- `CardAction.mill` — Target player mills N cards

**Mirkwood Meditator** (`mirkwoodMeditator`)

- `ContinuousEffect.setPowerToughness` — Set base P/T to literal values (only from another object or a count exists)
- `ContinuousEffect.setTypes` — Set types/subtypes rather than only gain them


**Misty Mountains Raider** (`mistyMountainsRaider`)

- `Selector.army` — Army (CardSubtype.army is also missing; used via Selector.subtype)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.amass` — Amass <subtype> N

**Moment of Glory** (`momentOfGlory`)

- `Ability.keywordFlashback` — Flashback with a cost
- `Ability.activateFromZone` — Ability that functions from the graveyard

**Most Decrepit Old Bird** (`mostDecrepitOldBird`)

- `SetPredicate.distinctNames` — Set-wide name constraints
- `Condition.countAtLeast` — At least N objects match a selector (graveyard size, lore, quest counters, …)
- `CardAction.mill` — Target player mills N cards

**My Precious** (`myPrecious`)

- `Selector.inExile` — An object in exile (wasCreatedByAction only covers this action's exile)

**Nasty Little Rabbit** (`nastyLittleRabbit`)

- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player
- `TraditionalCardDefinition.CardSubtype.Rabbit` — CardPart.subtype uses CardSubtype; Rabbit has no constructor

**Old Fat Spider** (`oldFatSpider`)

- `Selector.powerAtMost` — Power at most N (only powerAtLeast exists)
- `Trigger.becomeTarget` — When the selected object becomes the target of a spell or ability
- `ContinuousEffect.cantBeBlockedBy` — Can't be blocked by / if matching a selector (power at most/at least, tokens already exist as forbid block token this)

**Old Fat Spider Can't See Me** (`oldFatSpiderCanTSeeMe`)

- `TraditionalCardDefinition.sagaChapters` — Printed Saga chapters (roman numeral + actions); CardPart has no chapter
- `Trigger.sagaChapter` — When a lore counter is put / a (final) chapter ability resolves
- `CounterKind.lore` — Lore counters (putCounter only has plusOnePlusOne; CounterKind is used by CardAction)
- `ContinuousEffect.preventDamage` — Prevent (all) damage that would be dealt to/by a selector


**Orcrist, Goblin-cleaver** (`orcristGoblinCleaver`)

- `CardAction.chooseCreatureType` — Choose a creature type (as-enters or on resolution)
- `Selector.chosenType` — Objects of the chosen creature type
- `TraditionalCardDefinition.asEntersChoice` — As-this-enters replacement/choice on the face
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Ori, Keeper of Songs** (`oriKeeperOfSongs`)

- `Condition.enduringStory` — You have an enduring story (Storied is already a Keyword)

**Part in Friendship** (`partInFriendship`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.manaValue` — Mana-value comparisons
- `Trigger.onceEachTurn` — Limit a trigger to once each turn
- `ContinuousEffect.canPlay` — canPlay exists; need top-of-library + land/creature spell filters as a continuous permission
- `ContinuousEffect.reduceCostByValue` — Reduce cost by a computed value (flying power, opp artifacts, source power, gy count) — reduceCost only takes a literal Cost list
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)
- `CardAction.randomize` — Put on bottom in random order / pick a random card among
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `Selector.countOf` — Numeric value derived from a count or characteristic

**Patient Instructor** (`patientInstructor`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.recruit` — Recruit (draw, discard; if nonland discarded, create a Human Soldier)

**Pinecone Strike** (`pineconeStrike`)

- `ContinuousEffect.replace` — replace already exists; need a would-die / would-go-to-gy trigger which putToGraveyard covers — exile-instead is expressible if replace actions can exile (compiler may not)
- `CardAction.chooseModes` — Modal selection beyond exclusive chooseMode (one-or-both, choose-two-if, choose-both-if-teamwork)

**Plunder the Trollshaws** (`plunderTheTrollshaws`)

- `Ability.keywordFlashback` — Flashback with a cost
- `Ability.activateFromZone` — Ability that functions from the graveyard
- `ContinuousEffect.replaceDraw` — If you would draw (except the first in each draw step), draw N instead
- `Trigger.wouldDraw` — Would-draw replacement window (Trigger.draw is the actual event)

**Radagast of Rhosgobel** (`radagastOfRhosgobel`)

- `ContinuousEffect.gainAbilityIf` — Matching spells have flash / cost less with a 'first this turn' condition
- `Condition.firstThisTurn` — The first matching event this turn

**Rage into the Valley** (`rageIntoTheValley`)

- `Selector.army` — Army (CardSubtype.army is also missing; used via Selector.subtype)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.amass` — Amass <subtype> N

**Rhovanion Rampager** (`rhovanionRampager`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.army` — Army (CardSubtype.army is also missing; used via Selector.subtype)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.amass` — Amass <subtype> N

**Riddles in the Dark** (`riddlesInTheDark`)

- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)

**Roads Go Ever, Ever On** (`roadsGoEverEverOn`)

- `TraditionalCardDefinition.sagaChapters` — Printed Saga chapters (roman numeral + actions); CardPart has no chapter
- `Trigger.sagaChapter` — When a lore counter is put / a (final) chapter ability resolves
- `CounterKind.lore` — Lore counters (putCounter only has plusOnePlusOne; CounterKind is used by CardAction)
- `Ability.linkedExile` — Paired exile-until-leaves (enter trigger + leave trigger sharing exiled objects)
- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield
- `CardAction.returnExiled` — Return objects exiled by a linked action
- `CardAction.addManaPer` — Add mana for each matching object

**Roll-Roll-Roll-Roll** (`rollRollRollRoll`)

- `TraditionalCardDefinition.sagaChapters` — Printed Saga chapters (roman numeral + actions); CardPart has no chapter
- `Trigger.sagaChapter` — When a lore counter is put / a (final) chapter ability resolves
- `CounterKind.lore` — Lore counters (putCounter only has plusOnePlusOne; CounterKind is used by CardAction)
- `CardAction.exileThenReturn` — Exile then return at a later trigger (end step / leaves)

**Settle the Wreckage** (`settleTheWreckage`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat

**Silvan Reveler** (`silvanReveler`)

- `Ability.activateFromZone` — Activated ability that functions in the graveyard (or another non-battlefield zone)
- `CardAction.payThen` — You may pay a cost. If you do, perform actions (resolution-time optional payment, not an activated cost)

**Smaug the Magnificent** (`smaugTheMagnificent`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `Selector.countOf` — Numeric value derived from a count or characteristic

**Smaug, Wicked Worm** (`smaugWickedWorm`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat

**Sound the Trumpets** (`soundTheTrumpets`)

- `Selector.manaValue` — Mana-value comparisons
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.recruit` — Recruit (draw, discard; if nonland discarded, create a Human Soldier)

**Sting, Bilbo's Sword** (`stingBilboSSword`)

- `CounterKind.named` — Named counters other than +1/+1 (hone, trample, quest, shadow, finality, …)

**Stone-Giant of High Pass** (`stoneGiantOfHighPass`)

- `Selector.color` — Objects of a color / colorless
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Supper for Spiders** (`supperForSpiders`)

- `Selector.putFromBattlefieldThisTurn` — Cards put into a graveyard from the battlefield this turn (Shape.diedThisTurn is Condition-only)
- `CardAction.becomeWithAbility` — Lose other types, become Food artifacts, and gain a stated activated ability


**The Arkenstone** (`theArkenstone`)

- `Selector.inExile` — An object in exile (wasCreatedByAction only covers this action's exile)
- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player

**The Black Arrow** (`theBlackArrow`)

- `Trigger.dealtDamage` — When the selected object is dealt damage (Enrage / watch-damage)
- `CardAction.eventAmount` — Use the amount of damage/life/cards from the triggering event ('that much')


**The Eagles Are Coming!** (`theEaglesAreComing`)

- `Cost.optionalAdditional` — Optional additional cost (Kicker)
- `Ability.keywordKicker` — Kicker
- `Condition.kicked` — This spell was kicked
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.addManaPer` — Add mana for each matching object

**The Great Goblin** (`theGreatGoblin`)

- `Selector.army` — Army (CardSubtype.army is also missing; used via Selector.subtype)
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**The Lonely Mountain** (`theLonelyMountain`)

- `Condition.not` — Negation / unless (Condition has and, not or/not)
- `TraditionalCardDefinition.entersTappedUnless` — Enters tapped unless a condition (replace-enter is only compiled for always-tapped)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.addManaPer` — Add mana for each matching object

**The Lord of the Eagles** (`theLordOfTheEagles`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Cost.manaX` — Pay {X} / {X}{X} (ManaSymbol list has no X variable in Cost.mana as a bound value for later actions)
- `ContinuousEffect.reduceCostByValue` — Reduce cost by a computed value (flying power, opp artifacts, source power, gy count) — reduceCost only takes a literal Cost list
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**The Master of Lake-town** (`theMasterOfLakeTown`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Condition.countAtLeast` — At least N objects match a selector (graveyard size, lore, quest counters, …)
- `CardAction.mill` — Target player mills N cards

**The Misty Mountains Cold** (`theMistyMountainsCold`)

- `TraditionalCardDefinition.sagaChapters` — Printed Saga chapters (roman numeral + actions); CardPart has no chapter
- `Trigger.sagaChapter` — When a lore counter is put / a (final) chapter ability resolves
- `CounterKind.lore` — Lore counters (putCounter only has plusOnePlusOne; CounterKind is used by CardAction)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**The Mountain-king's Return** (`theMountainKingSReturn`)

- `TraditionalCardDefinition.sagaChapters` — Printed Saga chapters (roman numeral + actions); CardPart has no chapter
- `Trigger.sagaChapter` — When a lore counter is put / a (final) chapter ability resolves
- `CounterKind.lore` — Lore counters (putCounter only has plusOnePlusOne; CounterKind is used by CardAction)
- `Selector.manaValue` — Mana-value comparisons
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.recruit` — Recruit (draw, discard; if nonland discarded, create a Human Soldier)

**The Notary Hobbits** (`theNotaryHobbits`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.addManaPer` — Add mana for each matching object

**The Queen of Dale** (`theQueenOfDale`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.recruit` — Recruit (draw, discard; if nonland discarded, create a Human Soldier)
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**The Sackville-Bagginses** (`theSackvilleBagginses`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Thorin Oakenshield** (`thorinOakenshield`)

- `Condition.enduringStory` — You have an enduring story (Storied is already a Keyword)
- `Ability.keywordWard` — Ward with a cost (mana, discard-a-type, sacrifice legendary, poison, pay-or-discard)
- `Cost.wardNonmana` — Nonmana ward payments
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Thorin, Mountain-king** (`thorinMountainKing`)

- `Selector.attached` — Objects attached to a given object (inverse of hostOf)
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `Selector.countOf` — Numeric value derived from a count or characteristic
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Thranduil, Sindarin Liege** (`thranduilSindarinLiege`)

- `SetPredicate.distinctNames` — Set-wide name constraints
- `Selector.inExile` — An object in exile (wasCreatedByAction only covers this action's exile)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.mill` — Target player mills N cards
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Thranduil, the Elvenking** (`thranduilTheElvenking`)

- `ContinuousEffect.copyActivatedAbilities` — Gains the activated abilities of matching objects
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Through the Forest Gate** (`throughTheForestGate`)

- `SetPredicate.distinctNames` — Set-wide name constraints
- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)

**Tidings of War** (`tidingsOfWar`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.army` — Army (CardSubtype.army is also missing; used via Selector.subtype)
- `Ability.keywordFlashback` — Flashback with a cost
- `Ability.activateFromZone` — Ability that functions from the graveyard
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.amass` — Amass <subtype> N

**Tom, Bert, and William** (`tomBertAndWilliam`)

- `Selector.inHand` — A card in hand for Cost.discard
- `TraditionalCardDefinition.CardSubtype.Troll` — CardPart.subtype uses CardSubtype; Troll has no constructor

**Troll Negotiations** (`trollNegotiations`)

- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `Selector.countOf` — Numeric value derived from a count or characteristic

**Troop of Ponies** (`troopOfPonies`)

- `TraditionalCardDefinition.CardSubtype.Horse` — CardPart.subtype uses CardSubtype; Horse has no constructor

**Uncover the Moon-Letters** (`uncoverTheMoonLetters`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat


**Wizard's Staff** (`wizardSStaff`)

- `ContinuousEffect.extraTrigger` — Matching triggered abilities trigger an additional time

**enchantedRiverSGrasp** (`enchantedRiverSGrasp`)

- `ContinuousEffect.loseAbilities` — Selected object loses all abilities
- `ContinuousEffect.skipsUntap` — Selected permanents don't untap during the untap step
- `CardAction.removeCounter` — Remove counters from the selected object

**Óin the Brave** (`oinTheBrave`)

- `Selector.inHand` — A card in hand for Cost.discard
- `Condition.enduringStory` — You have an enduring story (Storied is already a Keyword)

### The Hobbit Eternal (HOC) (84 cards)

**Andúril, Flame of the West** (`andurilFlameOfTheWest`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Andúril, Narsil Reforged** (`andurilNarsilReforged`)

- `Condition.citysBlessing` — You have the city's blessing

**Aragorn and Arwen, Wed** (`aragornAndArwenWed`)

- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Aragorn, the Uniter** (`aragornTheUniter`)

- `Selector.color` — Objects of a color / colorless
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Arcane Signet** (`arcaneSignet`)

- `Selector.commander` — The selected player's commander
- `ContinuousEffect.restrictManaSpend` — Mana from an action may be spent only on matching events (current leftover is Elf-only)

**Arwen, Mortal Queen** (`arwenMortalQueen`)

- `TraditionalCardDefinition.entersWithCounters` — Enters with an indestructible counter
- `CounterKind.IndestructibleCounter` — Named counter kind beyond +1/+1
- `CardAction.removeCounter` — Remove counters from the selected object
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Arwen, Weaver of Hope** (`arwenWeaverOfHope`)

- `Selector.toughness` — Toughness comparisons / bind toughness as a number
- `ContinuousEffect.replaceEnterCounters` — As matching objects enter, they enter with extra counters
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Bag End Banquet** (`bagEndBanquet`)

- `CardAction.addManaPer` — Add mana for each matching object

**Banishing Light** (`banishingLight`)

- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield
- `Ability.linkedExile` — Paired exile-until-leaves (enter trigger + leave trigger sharing exiled objects)
- `CardAction.returnExiled` — Return objects exiled by a linked action

**Bilbo's Burglaring** (`bilboSBurglaring`)

- `CardAction.gainControl` — Gain control of selected objects
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)

**Bilbo's Ring** (`bilboSRing`)

- `Selector.attackingAlone` — A creature attacking alone
- `Trigger.attackAlone` — When the selected object attacks alone

**Bilbo, Fellow Conspirator** (`bilboFellowConspirator`)

- `ContinuousEffect.replaceTokenCreation` — If you would create a Food, also create a Treasure
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Bilbo, Unexpected Adventurer** (`bilboUnexpectedAdventurer`)

- `Selector.manaValue` — Mana-value comparisons
- `ContinuousEffect.cantBeBlockedBy` — Can't be blocked by / if matching a selector (power at most/at least, tokens already exist as forbid block token this)

**Bitter Downfall** (`bitterDownfall`)

- `Selector.damagedThisTurn` — Objects dealt damage this turn
- `ContinuousEffect.reduceCost` — reduceCost+if exists for tapped/attacking/died; missing damaged-this-turn shape

**Bolg, Erebor's Reckoning** (`bolgEreborsReckoning`)

- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player

**Call Forth the Tempest** (`callForthTheTempest`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.manaValue` — Mana-value comparisons
- `Selector.inExile` — An object in exile (wasCreatedByAction only covers this action's exile)
- `Ability.keywordCascade` — Cascade
- `CardAction.cascade` — Exile until a cheaper nonland; you may cast it
- `ContinuousEffect.canPlay` — canPlay exists; need top-of-library + land/creature spell filters as a continuous permission
- `ContinuousEffect.reduceCostByValue` — Reduce cost by a computed value (flying power, opp artifacts, source power, gy count) — reduceCost only takes a literal Cost list
- `CardAction.randomize` — Put on bottom in random order / pick a random card among
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `Selector.countOf` — Numeric value derived from a count or characteristic

**Cavern-Hoard Dragon** (`cavernHoardDragon`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Trigger.tokenEnters` — When a token the player controls enters (enter + token selector may suffice if token creation exists)
- `Cost.manaX` — Pay {X} / {X}{X} (ManaSymbol list has no X variable in Cost.mana as a bound value for later actions)
- `ContinuousEffect.reduceCostByValue` — Reduce cost by a computed value (flying power, opp artifacts, source power, gy count) — reduceCost only takes a literal Cost list
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Celeborn the Wise** (`celebornTheWise`)

- `Trigger.scry` — Whenever the selected player scries
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Chief of the Wilds** (`chiefOfTheWilds`)

- `ContinuousEffect.extraTrigger` — Matching triggered abilities trigger an additional time

**Colossal Whale** (`colossalWhale`)

- `Selector.defendingPlayer` — The defending player relative to an attacker
- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield
- `Ability.linkedExile` — Paired exile-until-leaves (enter trigger + leave trigger sharing exiled objects)
- `CardAction.returnExiled` — Return objects exiled by a linked action
- `TraditionalCardDefinition.CardSubtype.Whale` — CardPart.subtype uses CardSubtype; Whale has no constructor

**Dawn of a New Age** (`dawnOfANewAge`)

- `TraditionalCardDefinition.entersWithCounters` — Enters with hope counters per matching object
- `CounterKind.Hope` — Named counter kind beyond +1/+1
- `Selector.hasCounter` — Objects with / without a given counter kind
- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player
- `CardAction.removeCounter` — Remove counters from the selected object

**Delighted Halfling** (`delightedHalfling`)

- `ContinuousEffect.cantBeCountered` — Selected spells can't be countered
- `ContinuousEffect.restrictManaSpend` — Mana from an action may be spent only on matching events (current leftover is Elf-only)

**Dragon's Desire** (`dragonsDesire`)

- `CardAction.addManaPer` — Add mana for each matching object
- `Selector.countOf` — Numeric value derived from a count or characteristic

**Dragon-Cursed Halls** (`dragonCursedHalls`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Dwarven Warriors** (`dwarvenWarriors`)

- `Selector.powerAtMost` — Power at most N (only powerAtLeast exists)

**Dáin of the Ancient Halls** (`dainOfTheAncientHalls`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `Selector.countOf` — Numeric value derived from a count or characteristic
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Elven Chorus** (`elvenChorus`)

- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `ContinuousEffect.mayLookAtTop` — May look at the top card of the selected library any time
- `ContinuousEffect.canPlay` — canPlay exists; need top-of-library + land/creature spell filters as a continuous permission
- `ContinuousEffect.gainAbility` — gainAbility exists; granting a tap-add-mana activated ability to others needs Ability.activated as the granted ability (already in Ability) — compiler may not emit it
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)

**Elvish Archdruid** (`elvishArchdruid`)

- `CardAction.addManaPer` — Add mana for each matching object

**Errand-Rider of Gondor** (`errandRiderOfGondor`)

- `Selector.inHand` — An object in a hand


**Fiend Hunter** (`fiendHunter`)

- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield
- `Ability.linkedExile` — Paired exile-until-leaves (enter trigger + leave trigger sharing exiled objects)
- `CardAction.returnExiled` — Return objects exiled by a linked action

**Flame of Anor** (`flameOfAnor`)

- `CardAction.chooseModes` — Modal selection beyond exclusive chooseMode (one-or-both, choose-two-if, choose-both-if-teamwork)

**Flowering of the White Tree** (`floweringOfTheWhiteTree`)

- `Ability.keywordWard` — Ward with a cost (mana, discard-a-type, sacrifice legendary, poison, pay-or-discard)
- `Cost.wardNonmana` — Nonmana ward payments

**Fíli and Kíli, Joyous** (`filiAndKiliJoyous`)

- `ContinuousEffect.restrictManaSpend` — Mana from an action may be spent only on matching events (current leftover is Elf-only)

**Galadriel's Dismissal** (`galadrielSDismissal`)

- `Selector.attached` — Objects attached to a given object (inverse of hostOf)
- `Cost.optionalAdditional` — Optional additional cost (Kicker)
- `Ability.keywordKicker` — Kicker
- `Condition.kicked` — This spell was kicked

**Galadriel, Light of Valinor** (`galadrielLightOfValinor`)

- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Gandalf, Party Guest** (`gandalfPartyGuest`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.manaValue` — Mana-value comparisons
- `Selector.inHand` — An object in a hand
- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player


**Glamdring** (`glamdring`)

- `Selector.manaValue` — Mana-value comparisons
- `Selector.inHand` — An object in a hand
- `ContinuousEffect.reduceCostByValue` — Reduce cost by a computed value (flying power, opp artifacts, source power, gy count) — reduceCost only takes a literal Cost list
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `Selector.countOf` — Numeric value derived from a count or characteristic

**Goblin Cratermaker** (`goblinCratermaker`)

- `Selector.color` — Objects of a color / colorless

**Great Goblin, Foul-Hearted** (`greatGoblinFoulHearted`)

- `Selector.army` — Army (CardSubtype.army is also missing; used via Selector.subtype)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.amass` — Amass <subtype> N
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Gríma, Saruman's Footman** (`grimaSarumanSFootman`)

- `Selector.inExile` — An object in exile (wasCreatedByAction only covers this action's exile)
- `CardAction.randomize` — Put on bottom in random order / pick a random card among

**Haunt of the Dead Marshes** (`hauntOfTheDeadMarshes`)

- `Condition.any` — any with a legendary-you-control selector is already expressible; listed only if other gaps remain
- `Ability.activateFromZone` — Activated ability that functions in the graveyard (or another non-battlefield zone)
- `TraditionalCardDefinition.CardSubtype.Nightmare` — CardPart.subtype uses CardSubtype; Nightmare has no constructor

**Landroval, Horizon Witness** (`landrovalHorizonWitness`)

- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Last March of the Ents** (`lastMarchOfTheEnts`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.toughness` — Toughness comparisons / bind toughness as a number
- `Selector.inHand` — An object in a hand
- `ContinuousEffect.cantBeCountered` — Selected spells can't be countered
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `Selector.countOf` — Numeric value derived from a count or characteristic
- `Range.anyNumber` — Any number (range 0 ∞); Range.range needs a finite Nat hi

**Long-Lost Lances** (`longLostLances`)

- `Selector.attached` — Objects attached to a given object (inverse of hostOf)


**Lotho, Corrupt Shirriff** (`lothoCorruptShirriff`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Mentor of the Meek** (`mentorOfTheMeek`)

- `Selector.powerAtMost` — Power at most N (only powerAtLeast exists)
- `CardAction.payThen` — You may pay a cost. If you do, perform actions (resolution-time optional payment, not an activated cost)

**Minas Morgul, Dark Fortress** (`minasMorgulDarkFortress`)

- `CounterKind.named` — Named counters other than +1/+1 (hone, trample, quest, shadow, finality, …)

**Minas Tirith** (`minasTirith`)

- `Condition.not` — Negation / unless (Condition has and, not or/not)
- `TraditionalCardDefinition.entersTappedUnless` — Enters tapped unless a condition (replace-enter is only compiled for always-tapped)
- `Condition.attackedThisTurn` — You attacked with N or more creatures this turn

**Minas Tirith Garrison** (`minasTirithGarrison`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.inHand` — An object in a hand
- `ContinuousEffect.addPowerToughnessPer` — Pump / set PT from a count other than setPowerToughnessEqualToCount's lands-you-control leftover
- `Selector.countOf` — Numeric value derived from a count or characteristic
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed

**Mirkwood Elk** (`mirkwoodElk`)

- `Trigger.gainLife` — Whenever the selected player gains life
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `Selector.countOf` — Numeric value derived from a count or characteristic
- `TraditionalCardDefinition.CardSubtype.Elk` — CardPart.subtype uses CardSubtype; Elk has no constructor

**Mount Doom** (`mountDoom`)

- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)
- `Cost.life` — Cost.life exists; combination with tap+addMana one-of is expressible if Condition/action compile

**Mox Amber** (`moxAmber`)

- `ContinuousEffect.restrictManaSpend` — Mana from an action may be spent only on matching events (current leftover is Elf-only)

**Necklace of Girion** (`necklaceOfGirion`)

- `Selector.color` — Objects of a color / colorless

**Nimrodel Watcher** (`nimrodelWatcher`)

- `Trigger.scry` — Whenever the selected player scries
- `Trigger.onceEachTurn` — Limit a trigger to once each turn

**Olog-hai Crusher** (`ologHaiCrusher`)

- `Condition.not` — Negation / unless (Condition has and, not or/not)
- `TraditionalCardDefinition.entersTappedUnless` — Enters tapped unless a condition (replace-enter is only compiled for always-tapped)
- `TraditionalCardDefinition.CardSubtype.Troll` — CardPart.subtype uses CardSubtype; Troll has no constructor

**Orcish Bowmasters** (`orcishBowmasters`)

- `CardAction.amass` — Amass <subtype> N

**Orcish Siegemaster** (`orcishSiegemaster`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat

**Ori, Plate Stacker** (`oriPlateStacker`)

- `CardAction.eventAmount` — Use the amount of damage/life/cards from the triggering event ('that much')
- `Selector.countOf` — Numeric value derived from a count or characteristic
- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat


**Palantír of Orthanc** (`palantirOfOrthanc`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.manaValue` — Mana-value comparisons
- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player
- `CardAction.mill` — Target player mills N cards
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `Selector.countOf` — Numeric value derived from a count or characteristic

**Pelargir Survivor** (`pelargirSurvivor`)

- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CardAction.mill` — Target player mills N cards
- `ContinuousEffect.restrictManaSpend` — Mana from an action may be spent only on matching events (current leftover is Elf-only)
- `TraditionalCardDefinition.CardSubtype.Peasant` — CardPart.subtype uses CardSubtype; Peasant has no constructor

**Raise the Palisade** (`raiseThePalisade`)

- `CardAction.chooseCreatureType` — Choose a creature type (as-enters or on resolution)
- `Selector.chosenType` — Objects of the chosen creature type
- `TraditionalCardDefinition.asEntersChoice` — As-this-enters replacement/choice on the face

**Relic of Sauron** (`relicOfSauron`)

- `Selector.inHand` — A card in hand for Cost.discard
- `CardAction.addManaCombination` — Add N mana in any combination of listed types / any color

**Rivendell** (`rivendell`)

- `Condition.not` — Negation / unless (Condition has and, not or/not)
- `TraditionalCardDefinition.entersTappedUnless` — Enters tapped unless a condition (replace-enter is only compiled for always-tapped)
- `Condition.any` — any with a legendary-you-control selector is already expressible; listed only if other gaps remain

**Saruman of Many Colors** (`sarumanOfManyColors`)

- `Selector.manaValue` — Mana-value comparisons
- `Selector.inExile` — An object in exile (wasCreatedByAction only covers this action's exile)
- `Ability.keywordWard` — Ward with a cost (mana, discard-a-type, sacrifice legendary, poison, pay-or-discard)
- `Cost.wardNonmana` — Nonmana ward payments
- `CardAction.mill` — Target player mills N cards
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)

**Sauron, the Dark Lord** (`sauronTheDarkLord`)

- `Selector.army` — Army (CardSubtype.army is also missing; used via Selector.subtype)
- `Trigger.theRingTemptsYou` — Whenever the Ring tempts you / you choose a Ring-bearer
- `CardAction.theRingTemptsYou` — The Ring tempts you
- `Ability.keywordWard` — Ward with a cost (mana, discard-a-type, sacrifice legendary, poison, pay-or-discard)
- `Cost.wardNonmana` — Nonmana ward payments
- `CardAction.amass` — Amass <subtype> N

**Sauron, the Lidless Eye** (`sauronTheLidlessEye`)

- `CardAction.gainControl` — Gain control of selected objects
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)

**Shadow of the Enemy** (`shadowOfTheEnemy`)

- `Selector.inExile` — An object in exile (wasCreatedByAction only covers this action's exile)

**Smaug the Impenetrable** (`smaugTheImpenetrable`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat

**Smite the Deathless** (`smiteTheDeathless`)

- `ContinuousEffect.replace` — replace already exists; need a would-die / would-go-to-gy trigger which putToGraveyard covers — exile-instead is expressible if replace actions can exile (compiler may not)

**Stern Scolding** (`sternScolding`)

- `Selector.powerAtMost` — Power at most N (only powerAtLeast exists)
- `Selector.toughness` — Toughness comparisons / bind toughness as a number

**The Black Gate** (`theBlackGate`)

- `Condition.not` — Negation / unless (Condition has and, not or/not)
- `TraditionalCardDefinition.entersTappedUnless` — Enters tapped unless a condition (replace-enter is only compiled for always-tapped)
- `CardAction.payThen` — You may pay a cost. If you do, perform actions (resolution-time optional payment, not an activated cost)
- `TraditionalCardDefinition.CardSubtype.Gate` — CardPart.subtype uses CardSubtype; Gate has no constructor

**The Gaffer** (`theGaffer`)

- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player
- `TraditionalCardDefinition.CardSubtype.Peasant` — CardPart.subtype uses CardSubtype; Peasant has no constructor

**The One Ring** (`theOneRing`)

- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player

**The Reaver Cleaver** (`theReaverCleaver`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat

**The Shire** (`theShire`)

- `Cost.tapOther` — Tap another matching permanent (not the tap symbol on the source)
- `Condition.not` — Negation / unless (Condition has and, not or/not)
- `TraditionalCardDefinition.entersTappedUnless` — Enters tapped unless a condition (replace-enter is only compiled for always-tapped)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Thorin, Company's Leader** (`thorinCompanySLeader`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Thorin, King of Durin's Folk** (`thorinKingOfDurinsFolk`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Thranduil the Strategist** (`thranduilTheStrategist`)

- `ContinuousEffect.gainAbility` — gainAbility exists; granting a tap-add-mana activated ability to others needs Ability.activated as the granted ability (already in Ability) — compiler may not emit it
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Tom Bombadil** (`tomBombadil`)

- `Trigger.onceEachTurn` — Limit a trigger to once each turn
- `ContinuousEffect.canPlay` — canPlay exists; need top-of-library + land/creature spell filters as a continuous permission
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)
- `CardAction.randomize` — Put on bottom in random order / pick a random card among
- `Condition.countAtLeast` — N or more lore counters among Sagas you control

**Treasure Vault** (`treasureVault`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Cost.manaX` — Pay {X} / {X}{X} (ManaSymbol list has no X variable in Cost.mana as a bound value for later actions)

**Troll of Khazad-dûm** (`trollOfKhazadDum`)

- `ContinuousEffect.cantBeBlockedExceptBy` — Can't be blocked except by N or more creatures (menace is Keyword for N=2)
- `TraditionalCardDefinition.CardSubtype.Troll` — CardPart.subtype uses CardSubtype; Troll has no constructor

**Witch-king of Angmar** (`witchKingOfAngmar`)

- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player
- `Trigger.theRingTemptsYou` — Whenever the Ring tempts you / you choose a Ring-bearer
- `CardAction.theRingTemptsYou` — The Ring tempts you
- `Trigger.scry` — Whenever the selected player scries
- `Selector.inHand` — A card in hand for Cost.discard
- `ContinuousEffect.cantBeBlockedExceptBy` — Can't be blocked except by N or more creatures (menace is Keyword for N=2)
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)
- `TraditionalCardDefinition.CardSubtype.Wraith` — CardPart.subtype uses CardSubtype; Wraith has no constructor
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Witch-king, Bringer of Ruin** (`witchKingBringerOfRuin`)

- `Selector.defendingPlayer` — The defending player relative to an attacker
- `TraditionalCardDefinition.CardSubtype.Wraith` — CardPart.subtype uses CardSubtype; Wraith has no constructor
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**fogOnTheBarrowDowns** (`fogOnTheBarrowDowns`)

- `ContinuousEffect.forbidAttack` — Can't attack / attacks-if-able (forbid exists for Trigger; need an attack event plus a restriction combinator)
- `Condition.controlCount` — Controller controls N or more matching objects
- `ContinuousEffect.setSubtypes` — Overwrite subtypes (gainSubtype only adds)

### Marvel Super Heroes (MSH) (227 cards)

**A.I.M. Scientists** (`aIMScientists`)

- `Selector.inHand` — A card in hand for Cost.discard
- `CardAction.connive` — Connive
- `TraditionalCardDefinition.CardSubtype.Scientist` — CardPart.subtype uses CardSubtype; Scientist has no constructor

**A.I.M. Synthoids** (`aIMSynthoids`)

- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CardAction.surveil` — Surveil N
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)

**Abomination, Terrifying Titan** (`abominationTerrifyingTitan`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn
- `TraditionalCardDefinition.CardSubtype.Gamma` — CardPart.subtype uses CardSubtype; Gamma has no constructor

**Absorbing Man** (`absorbingMan`)

- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player
- `CardAction.copy` — Copy a permanent, spell, or ability
- `ContinuousEffect.setPowerToughness` — Set base P/T to literal values (only from another object or a count exists)
- `ContinuousEffect.setTypes` — Set types/subtypes rather than only gain them

**Aerial Doombot** (`aerialDoombot`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn

**Agent 13, Sharon Carter** (`agent13SharonCarter`)

- `Selector.attackingAlone` — A creature attacking alone
- `Trigger.attackAlone` — When the selected object attacks alone
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.investigate` — Investigate / create a Clue

**Agent Maria Hill** (`agentMariaHill`)

- `Trigger.becomeTapped` — When the selected object becomes tapped (including tapped to pay a cost)


**Agents of HYDRA** (`agentsOfHYDRA`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Agents of S.H.I.E.L.D.** (`agentsOfSHIELD`)

- `Selector.attackingAlone` — A creature attacking alone
- `Trigger.attackAlone` — When the selected object attacks alone

**Alien Invasion** (`alienInvasion`)

- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player
- `ContinuousEffect.forbidAttack` — Can't attack / attacks-if-able (forbid exists for Trigger; need an attack event plus a restriction combinator)
- `Condition.controlCount` — Controller controls N or more matching objects
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Ant-Man's Army** (`antManSArmy`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Ant-Man, Colony Commander** (`antManColonyCommander`)

- `Trigger.onceEachTurn` — Limit a trigger to once each turn
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Arc Reactor** (`arcReactor`)

- `Ability.keywordImprovise` — Improvise
- `Cost.tapArtifactsForGeneric` — Tap artifacts to pay generic

**Ares, God of War** (`aresGodOfWar`)

- `ContinuousEffect.forbidAttack` — Can't attack / attacks-if-able (forbid exists for Trigger; need an attack event plus a restriction combinator)
- `Condition.controlCount` — Controller controls N or more matching objects

**Armor Wars** (`armorWars`)

- `TraditionalCardDefinition.sagaChapters` — Printed Saga chapters (roman numeral + actions); CardPart has no chapter
- `Trigger.sagaChapter` — When a lore counter is put / a (final) chapter ability resolves
- `CounterKind.lore` — Lore counters (putCounter only has plusOnePlusOne; CounterKind is used by CardAction)
- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.manaValue` — Mana-value comparisons
- `CardAction.addManaPer` — Add mana for each matching object
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)
- `TraditionalCardDefinition.CardSubtype.Saga` — CardPart.subtype uses CardSubtype; Saga has no constructor

**Arnim Zola, Bio-Fanatic** (`arnimZolaBioFanatic`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `TraditionalCardDefinition.CardSubtype.Scientist` — CardPart.subtype uses CardSubtype; Scientist has no constructor

**Atlantis Attacks** (`atlantisAttacks`)

- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork / Crew)
- `Ability.keywordTeamwork` — Teamwork N as an optional additional cost
- `Condition.castWithTeamwork` — This spell was cast using teamwork
- `CardAction.chooseModes` — Modal selection beyond exclusive chooseMode (one-or-both, choose-two-if, choose-both-if-teamwork)


**Avengers Assemble!** (`avengersAssemble`)

- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player

**Avengers Disassembled** (`avengersDisassembled`)

- `CardAction.chooseModes` — Modal selection beyond exclusive chooseMode (one-or-both, choose-two-if, choose-both-if-teamwork)

**Avengers Tower** (`avengersTower`)

- `SetPredicate.distinctNames` — Set-wide name constraints
- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)
- `ContinuousEffect.restrictManaSpend` — Mana from an action may be spent only on matching events (current leftover is Elf-only)

**Avengers: Under Siege** (`avengersUnderSiege`)

- `TraditionalCardDefinition.sagaChapters` — Printed Saga chapters (roman numeral + actions); CardPart has no chapter
- `Trigger.sagaChapter` — When a lore counter is put / a (final) chapter ability resolves
- `CounterKind.lore` — Lore counters (putCounter only has plusOnePlusOne; CounterKind is used by CardAction)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.addManaPer` — Add mana for each matching object
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)
- `TraditionalCardDefinition.CardSubtype.Saga` — CardPart.subtype uses CardSubtype; Saga has no constructor

**Baron Helmut Zemo** (`baronHelmutZemo`)

- `Selector.inHand` — An object in a hand
- `Selector.inExile` — An object in exile (wasCreatedByAction only covers this action's exile)
- `Selector.color` — Objects of a color / colorless
- `Trigger.onceEachTurn` — Limit a trigger to once each turn
- `Ability.keywordBoast` — Boast
- `CardAction.connive` — Connive
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Baron Strucker, HYDRA Overlord** (`baronStruckerHYDRAOverlord`)

- `Trigger.onceEachTurn` — Limit a trigger to once each turn
- `Selector.inHand` — A card in hand for Cost.discard
- `CardAction.connive` — Connive

**Baxter Building** (`baxterBuilding`)

- `Selector.toughness` — Toughness comparisons / bind toughness as a number
- `CardAction.addManaCombination` — Add N mana in any combination of listed types / any color

**Beast, Erudite Aerialist** (`beastEruditeAerialist`)

- `TraditionalCardDefinition.CardSubtype.Mutant` — CardPart.subtype uses CardSubtype; Mutant has no constructor
- `TraditionalCardDefinition.CardSubtype.Scientist` — CardPart.subtype uses CardSubtype; Scientist has no constructor

**Black Panther, Hope Enduring** (`blackPantherHopeEnduring`)

- `ContinuousEffect.preventDamage` — Prevent (all) damage that would be dealt to/by a selector

**Black Panther, Vanguard** (`blackPantherVanguard`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Black Widow, Double Agent** (`blackWidowDoubleAgent`)

- `Selector.attackingAlone` — A creature attacking alone
- `Trigger.attackAlone` — When the selected object attacks alone

**Black Widow, Super Spy** (`blackWidowSuperSpy`)

- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `Selector.inExile` — An object in exile (wasCreatedByAction only covers this action's exile)
- `CardAction.exileUntil` — Exile from the top until a matching card (nonland leftover)


**Bold Biochemist** (`boldBiochemist`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn
- `TraditionalCardDefinition.CardSubtype.Scientist` — CardPart.subtype uses CardSubtype; Scientist has no constructor

**Borough Backup** (`boroughBackup`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Brave Brawler** (`braveBrawler`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn

**Bruce Banner** (`bruceBanner`)

- `TraditionalCardDefinition.otherFace` — Second face of a transforming DFC (CardPart.alternative is Adventure-only)
- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Cost.manaX` — Pay {X} / {X}{X} (ManaSymbol list has no X variable in Cost.mana as a bound value for later actions)
- `CardAction.transform` — Transform this permanent
- `TraditionalCardDefinition.CardSubtype.Scientist` — CardPart.subtype uses CardSubtype; Scientist has no constructor

**Bullseye, Death Dealer** (`bullseyeDeathDealer`)

- `TraditionalCardDefinition.CardSubtype.Assassin` — CardPart.subtype uses CardSubtype; Assassin has no constructor


**Captain America's Shield** (`captainAmericaSShield`)

- `Selector.defendingPlayer` — The defending player relative to an attacker

**Captain America, Living Legend** (`captainAmericaLivingLegend`)

- `Trigger.becomeTapped` — When the selected object becomes tapped (including tapped to pay a cost)

**Captain America, Super-Soldier** (`captainAmericaSuperSoldier`)

- `TraditionalCardDefinition.entersWithCounters` — Enters with shield counters
- `CounterKind.Shield` — Named counter kind beyond +1/+1
- `Selector.hasCounter` — Objects with / without a given counter kind
- `CardAction.removeCounter` — Remove counters from the selected object

**Captain America, Wings of Freedom** (`captainAmericaWingsOfFreedom`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Ability.keywordWard` — Ward with a cost (mana, discard-a-type, sacrifice legendary, poison, pay-or-discard)
- `Cost.wardNonmana` — Nonmana ward payments

**Captain Mar-Vell, Space-Born** (`captainMarVellSpaceBorn`)

- `ContinuousEffect.gainAbilityIf` — Matching spells have flash / cost less with a 'first this turn' condition


**Captain Marvel, Earth's Protector** (`captainMarvelEarthSProtector`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn

**Castle Doom** (`castleDoom`)

- `Selector.color` — Objects of a color / colorless
- `Selector.named` — Objects with a given name
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `ContinuousEffect.restrictManaSpend` — Mana from an action may be spent only on matching events (current leftover is Elf-only)

**Claim the Kingdom** (`claimTheKingdom`)

- `TraditionalCardDefinition.CardSubtype.Plan` — CardPart.subtype uses CardSubtype; Plan has no constructor

**Cloak and Dagger, Entwined** (`cloakAndDaggerEntwined`)

- `Selector.inHand` — An object in a hand
- `Ability.linkedExile` — Paired exile-until-leaves (enter trigger + leave trigger sharing exiled objects)
- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield
- `CardAction.returnExiled` — Return objects exiled by a linked action

**Colleen Wing, Street Samurai** (`colleenWingStreetSamurai`)

- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)
- `TraditionalCardDefinition.CardSubtype.Samurai` — CardPart.subtype uses CardSubtype; Samurai has no constructor

**Construct a Cosmic Cube** (`constructACosmicCube`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `TraditionalCardDefinition.CardSubtype.Plan` — CardPart.subtype uses CardSubtype; Plan has no constructor

**Cosmic Cube** (`cosmicCube`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `SetPredicate.distinctNames` — Set-wide name constraints
- `Selector.manaValue` — Mana-value comparisons
- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `Ability.keywordWard` — Ward with a cost (mana, discard-a-type, sacrifice legendary, poison, pay-or-discard)
- `Cost.wardNonmana` — Nonmana ward payments
- `ContinuousEffect.reduceCostByValue` — Reduce cost by a computed value (flying power, opp artifacts, source power, gy count) — reduceCost only takes a literal Cost list
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)
- `CardAction.randomize` — Put on bottom in random order / pick a random card among
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `Selector.countOf` — Numeric value derived from a count or characteristic

**Crossbones, Malicious Mercenary** (`crossbonesMaliciousMercenary`)

- `Trigger.onceEachTurn` — Limit a trigger to once each turn
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)
- `TraditionalCardDefinition.CardSubtype.Mercenary` — CardPart.subtype uses CardSubtype; Mercenary has no constructor

**Crowd of True Believers** (`crowdOfTrueBelievers`)

- `Selector.attackingAlone` — A creature attacking alone
- `Trigger.attackAlone` — When the selected object attacks alone

**Cruel Alliance** (`cruelAlliance`)

- `Selector.manaValue` — Mana-value comparisons
- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork / Crew)
- `Ability.keywordTeamwork` — Teamwork N as an optional additional cost
- `Condition.castWithTeamwork` — This spell was cast using teamwork

**Daredevil, Man Without Fear** (`daredevilManWithoutFear`)

- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `ContinuousEffect.mayLookAtTop` — May look at the top card of the selected library any time
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)

**Death to Our Enemies** (`deathToOurEnemies`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `TraditionalCardDefinition.CardSubtype.Plan` — CardPart.subtype uses CardSubtype; Plan has no constructor

**Decoy Ploy** (`decoyPloy`)

- `CardAction.chooseModes` — Modal selection beyond exclusive chooseMode (one-or-both, choose-two-if, choose-both-if-teamwork)

**Dependable Quinjet** (`dependableQuinjet`)

- `Cost.tapPowerTotal` — Tap creatures with total power N or more
- `Ability.keywordCrew` — Crew N
- `ContinuousEffect.setPowerToughness` — Set base P/T to literal values (only from another object or a count exists)
- `ContinuousEffect.setTypes` — Set types/subtypes rather than only gain them

**Doc Samson, Super Psychiatrist** (`docSamsonSuperPsychiatrist`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `TraditionalCardDefinition.CardSubtype.Gamma` — CardPart.subtype uses CardSubtype; Gamma has no constructor
- `TraditionalCardDefinition.CardSubtype.Doctor` — CardPart.subtype uses CardSubtype; Doctor has no constructor

**Doctor Doom** (`doctorDoom`)

- `Selector.color` — Objects of a color / colorless
- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `TraditionalCardDefinition.CardSubtype.Scientist` — CardPart.subtype uses CardSubtype; Scientist has no constructor

**Doom Reigns Supreme** (`doomReignsSupreme`)

- `Selector.inExile` — An object in exile (wasCreatedByAction only covers this action's exile)
- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)
- `TraditionalCardDefinition.CardSubtype.Plan` — CardPart.subtype uses CardSubtype; Plan has no constructor

**Earth's Mightiest Heroes** (`earthSMightiestHeroes`)

- `SetPredicate.distinctNames` — Set-wide name constraints
- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork / Crew)
- `Ability.keywordTeamwork` — Teamwork N as an optional additional cost
- `Condition.castWithTeamwork` — This spell was cast using teamwork

**Echo, Perceptive Prodigy** (`echoPerceptiveProdigy`)

- `CardAction.copy` — Copy a permanent, spell, or ability

**Elektra, Daughter of the Hand** (`elektraDaughterOfTheHand`)

- `Selector.powerAtMost` — Power at most N (only powerAtLeast exists)
- `Ability.keywordSneak` — Sneak
- `TraditionalCardDefinition.CardSubtype.Ninja` — CardPart.subtype uses CardSubtype; Ninja has no constructor

**Epic Fight** (`epicFight`)

- `CardAction.chooseModes` — Modal selection beyond exclusive chooseMode (one-or-both, choose-two-if, choose-both-if-teamwork)

**Evil's Thrall** (`evilSThrall`)

- `Selector.manaValue` — Mana-value comparisons
- `CardAction.gainControl` — Gain control of selected objects

**Falcon's Wing Harness** (`falconSWingHarness`)

- `Trigger.becomeTarget` — When the selected object becomes the target of a spell or ability
- `Ability.keywordWard` — Ward with a cost (mana, discard-a-type, sacrifice legendary, poison, pay-or-discard)
- `Cost.wardNonmana` — Nonmana ward payments

**Falcon, Winged Wonder** (`falconWingedWonder`)

- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CardAction.surveil` — Surveil N
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)

**Fin Fang Foom** (`finFangFoom`)

- `TraditionalCardDefinition.CardSubtype.Alien` — CardPart.subtype uses CardSubtype; Alien has no constructor

**Frozen in Ice** (`frozenInIce`)

- `ContinuousEffect.loseAbilities` — Selected object loses all abilities
- `ContinuousEffect.skipsUntap` — Selected permanents don't untap during the untap step


**Go Nuts!** (`goNuts`)

- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork / Crew)
- `Ability.keywordTeamwork` — Teamwork N as an optional additional cost
- `Condition.castWithTeamwork` — This spell was cast using teamwork
- `CardAction.chooseModes` — Modal selection beyond exclusive chooseMode (one-or-both, choose-two-if, choose-both-if-teamwork)

**Grim Reaper, Lethal Legionnaire** (`grimReaperLethalLegionnaire`)

- `ContinuousEffect.replace` — replace already exists; need a would-die / would-go-to-gy trigger which putToGraveyard covers — exile-instead is expressible if replace actions can exile (compiler may not)
- `CounterKind.named` — Named counters other than +1/+1 (hone, trample, quest, shadow, finality, …)

**Guerrilla Gorilla** (`guerrillaGorilla`)

- `TraditionalCardDefinition.CardSubtype.Ape` — CardPart.subtype uses CardSubtype; Ape has no constructor

**H.E.R.B.I.E. Scout Unit** (`hERBIEScoutUnit`)

- `Selector.inHand` — An object in a hand

**HULK SMASH!** (`hULKSMASH`)

- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork / Crew)
- `Ability.keywordTeamwork` — Teamwork N as an optional additional cost
- `Condition.castWithTeamwork` — This spell was cast using teamwork
- `CardAction.chooseModes` — Modal selection beyond exclusive chooseMode (one-or-both, choose-two-if, choose-both-if-teamwork)
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `Selector.countOf` — Numeric value derived from a count or characteristic


**HYDRA Infiltration** (`hYDRAInfiltration`)

- `Selector.attackingAlone` — A creature attacking alone
- `Trigger.attackAlone` — When the selected object attacks alone

**HYDRA Troopers** (`hYDRATroopers`)

- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.mill` — Target player mills N cards

**Hawkeye's Bow** (`hawkeyeSBow`)

- `Trigger.becomeTapped` — When the selected object becomes tapped (including tapped to pay a cost)
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)

**Hawkeye, Master Marksman** (`hawkeyeMasterMarksman`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Trigger.becomeTapped` — When the selected object becomes tapped (including tapped to pay a cost)

**Hawkeye, Young Avenger** (`hawkeyeYoungAvenger`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `ContinuousEffect.modifyDamage` — Replacement that changes how much damage is dealt
- `CardAction.eventAmount` — Bind/use an amount from a previous action or trigger (that much, excess, sacrificed power)

**Helicarrier Strike** (`helicarrierStrike`)

- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork / Crew)
- `Ability.keywordTeamwork` — Teamwork N as an optional additional cost
- `Condition.castWithTeamwork` — This spell was cast using teamwork

**Hellcat, Undying Vigilante** (`hellcatUndyingVigilante`)

- `Selector.hasCounter` — Objects with / without a given counter kind
- `ContinuousEffect.loseAbilities` — Selected object loses all abilities

**Hercules, Prince of Power** (`herculesPrinceOfPower`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn
- `TraditionalCardDefinition.CardSubtype.Demigod` — CardPart.subtype uses CardSubtype; Demigod has no constructor


**Heroic Feast** (`heroicFeast`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Trigger.gainLife` — Whenever the selected player gains life
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Hex Magic** (`hexMagic`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.inHand` — An object in a hand
- `TraditionalCardDefinition.CardSubtype.Arcane` — CardPart.subtype uses CardSubtype; Arcane has no constructor

**Hire a Crew** (`hireACrew`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Hour of Defeat** (`hourOfDefeat`)

- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CardAction.surveil` — Surveil N
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)

**Hulk, Gamma Goliath** (`hulkGammaGoliath`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn
- `TraditionalCardDefinition.CardSubtype.Gamma` — CardPart.subtype uses CardSubtype; Gamma has no constructor
- `TraditionalCardDefinition.CardSubtype.Berserker` — CardPart.subtype uses CardSubtype; Berserker has no constructor

**Hulkling, Burgeoning Bruiser** (`hulklingBurgeoningBruiser`)

- `Selector.powerAtMost` — Power at most N (only powerAtLeast exists)
- `TraditionalCardDefinition.CardSubtype.Skrull` — CardPart.subtype uses CardSubtype; Skrull has no constructor

**Human Torch, Johnny Storm** (`humanTorchJohnnyStorm`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn

**Hydraulic Helper** (`hydraulicHelper`)

- `ContinuousEffect.restrictManaSpend` — Mana from an action may be spent only on matching events (current leftover is Elf-only)

**I Am Iron Man** (`iAmIronMan`)

- `Selector.toughness` — Toughness comparisons / bind toughness as a number
- `ContinuousEffect.setPowerToughness` — Set base P/T to literal values (only from another object or a count exists)
- `ContinuousEffect.setTypes` — Set types/subtypes rather than only gain them

**Invisible Woman, Sue Storm** (`invisibleWomanSueStorm`)

- `Selector.color` — Objects of a color / colorless
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Iron Fist, Living Weapon** (`ironFistLivingWeapon`)

- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `Selector.countOf` — Numeric value derived from a count or characteristic

**Iron Lad, Diverging Destiny** (`ironLadDivergingDestiny`)

- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `ContinuousEffect.mayLookAtTop` — May look at the top card of the selected library any time
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)

**Iron Man Armor** (`ironManArmor`)

- `ContinuousEffect.setPowerToughness` — Set base P/T to literal values (only from another object or a count exists)
- `ContinuousEffect.setTypes` — Set types/subtypes rather than only gain them

**Iron Man, Master of Machines** (`ironManMasterOfMachines`)

- `ContinuousEffect.addPowerToughnessPer` — Pump / set PT from a count other than setPowerToughnessEqualToCount's lands-you-control leftover
- `Selector.countOf` — Numeric value derived from a count or characteristic

**Ironheart, Clever Champion** (`ironheartCleverChampion`)

- `Ability.keywordImprovise` — Improvise
- `Cost.tapArtifactsForGeneric` — Tap artifacts to pay generic

**Jennifer Walters** (`jenniferWalters`)

- `TraditionalCardDefinition.otherFace` — Second face of a transforming DFC (CardPart.alternative is Adventure-only)
- `ContinuousEffect.forbidCast` — Players matching a selector can't cast spells matching a selector
- `CardAction.transform` — Transform this permanent

**Jessica Jones, Private Eye** (`jessicaJonesPrivateEye`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CounterKind.named` — Named counters other than +1/+1 (hone, trample, quest, shadow, finality, …)
- `TraditionalCardDefinition.CardSubtype.Detective` — CardPart.subtype uses CardSubtype; Detective has no constructor

**Justice, Vance Astrovik** (`justiceVanceAstrovik`)

- `TraditionalCardDefinition.CardSubtype.Mutant` — CardPart.subtype uses CardSubtype; Mutant has no constructor


**Ka-Zar of the Savage Land** (`kaZarOfTheSavageLand`)

- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `ContinuousEffect.mayLookAtTop` — May look at the top card of the selected library any time
- `ContinuousEffect.canPlay` — canPlay exists; need top-of-library + land/creature spell filters as a continuous permission
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)
- `TraditionalCardDefinition.CardSubtype.Barbarian` — CardPart.subtype uses CardSubtype; Barbarian has no constructor

**Kang the Conqueror** (`kangTheConqueror`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn

**Kang, Temporal Tyrant** (`kangTemporalTyrant`)

- `CardAction.connive` — Connive
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)

**Kid Loki** (`kidLoki`)

- `Selector.hasCounter` — Objects with / without a given counter kind
- `Selector.receivedCounterThisTurn` — Objects you put +1/+1 counters on this turn


**Killmonger, Scourge of Wakanda** (`killmongerScourgeOfWakanda`)

- `TraditionalCardDefinition.CardSubtype.Mercenary` — CardPart.subtype uses CardSubtype; Mercenary has no constructor

**King T'Challa** (`kingTChalla`)

- `TraditionalCardDefinition.otherFace` — Second face of a transforming DFC (CardPart.alternative is Adventure-only)
- `CardAction.transform` — Transform this permanent
- `TraditionalCardDefinition.CardSubtype.Noble` — CardPart.subtype uses CardSubtype; Noble has no constructor

**Klaw, Sonic Subjugator** (`klawSonicSubjugator`)

- `Selector.inHand` — An object in a hand

**Knight of Wundagore** (`knightOfWundagore`)

- `Trigger.onceEachTurn` — Limit a trigger to once each turn
- `TraditionalCardDefinition.CardSubtype.Cat` — CardPart.subtype uses CardSubtype; Cat has no constructor

**Leader, Super-Genius** (`leaderSuperGenius`)

- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player
- `CardAction.connive` — Connive
- `TraditionalCardDefinition.CardSubtype.Gamma` — CardPart.subtype uses CardSubtype; Gamma has no constructor
- `TraditionalCardDefinition.CardSubtype.Scientist` — CardPart.subtype uses CardSubtype; Scientist has no constructor

**Loki Laufeyson** (`lokiLaufeyson`)

- `Selector.manaValue` — Mana-value comparisons
- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn
- `ContinuousEffect.reduceCostByValue` — Reduce cost by a computed value (flying power, opp artifacts, source power, gy count) — reduceCost only takes a literal Cost list
- `TraditionalCardDefinition.CardSubtype.Sorcerer` — CardPart.subtype uses CardSubtype; Sorcerer has no constructor

**Loki, God of Mischief** (`lokiGodOfMischief`)

- `Trigger.becomeTarget` — When the selected object becomes the target of a spell or ability
- `Trigger.onceEachTurn` — Limit a trigger to once each turn
- `TraditionalCardDefinition.CardSubtype.Sorcerer` — CardPart.subtype uses CardSubtype; Sorcerer has no constructor

**Luke Cage, Power Man** (`lukeCagePowerMan`)

- `Selector.attackingAlone` — A creature attacking alone
- `Trigger.attackAlone` — When the selected object attacks alone

**M.O.D.O.K.** (`mODOK`)

- `Selector.inHand` — A card in hand for Cost.discard
- `CardAction.connive` — Connive

**Madame Hydra** (`madameHydra`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Madame Masque** (`madameMasque`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.connive` — Connive

**Mister Fantastic, Reed Richards** (`misterFantasticReedRichards`)

- `Trigger.tokenEnters` — When a token the player controls enters (enter + token selector may suffice if token creation exists)
- `TraditionalCardDefinition.CardSubtype.Scientist` — CardPart.subtype uses CardSubtype; Scientist has no constructor

**Mister Hyde, Monster Within** (`misterHydeMonsterWithin`)

- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player
- `CardAction.removeCounter` — Remove counters from the selected object

**Misty Knight, Hero for Hire** (`mistyKnightHeroForHire`)

- `Selector.inHand` — A card in hand for Cost.discard
- `TraditionalCardDefinition.CardSubtype.Detective` — CardPart.subtype uses CardSubtype; Detective has no constructor

**Mjölnir, Hammer of Thor** (`mjLnirHammerOfThor`)

- `Selector.worthy` — Worthy (Marvel)
- `ContinuousEffect.modifyDamage` — Replacement that changes how much damage is dealt


**Mole Man, Moloid Master** (`moleManMoloidMaster`)

- `Selector.named` — Objects with a given name
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.mill` — Target player mills N cards

**Monica Rambeau** (`monicaRambeau`)

- `TraditionalCardDefinition.otherFace` — Second face of a transforming DFC (CardPart.alternative is Adventure-only)
- `CardAction.transform` — Transform this permanent

**Moon Girl and Devil Dinosaur** (`moonGirlAndDevilDinosaur`)

- `Trigger.onceEachTurn` — Limit a trigger to once each turn
- `ContinuousEffect.setPowerToughness` — Set base P/T to literal values (only from another object or a count exists)
- `ContinuousEffect.setTypes` — Set types/subtypes rather than only gain them

**Moonstone, Harsh Mistress** (`moonstoneHarshMistress`)

- `TraditionalCardDefinition.CardSubtype.Doctor` — CardPart.subtype uses CardSubtype; Doctor has no constructor

**Ms. Marvel, Kamala Khan** (`msMarvelKamalaKhan`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.inHand` — An object in a hand
- `ContinuousEffect.handSize` — Set / remove maximum hand size
- `ContinuousEffect.addPowerToughnessPer` — Pump / set PT from a count other than setPowerToughnessEqualToCount's lands-you-control leftover
- `Selector.countOf` — Numeric value derived from a count or characteristic
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `TraditionalCardDefinition.CardSubtype.Mutant` — CardPart.subtype uses CardSubtype; Mutant has no constructor
- `TraditionalCardDefinition.CardSubtype.Inhuman` — CardPart.subtype uses CardSubtype; Inhuman has no constructor

**Multiversal Incursion** (`multiversalIncursion`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.copy` — Copy a permanent, spell, or ability

**Murdock's Crusade** (`murdockSCrusade`)

- `Selector.toughness` — Toughness comparisons / bind toughness as a number
- `Selector.manaValue` — Mana-value comparisons
- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork / Crew)
- `Ability.keywordTeamwork` — Teamwork N as an optional additional cost
- `Condition.castWithTeamwork` — This spell was cast using teamwork
- `CardAction.chooseModes` — Modal selection beyond exclusive chooseMode (one-or-both, choose-two-if, choose-both-if-teamwork)

**Namor the Sub-Mariner** (`namorTheSubMariner`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `ContinuousEffect.addPowerToughnessPer` — Pump / set PT from a count other than setPowerToughnessEqualToCount's lands-you-control leftover
- `Selector.countOf` — Numeric value derived from a count or characteristic
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `TraditionalCardDefinition.CardSubtype.Mutant` — CardPart.subtype uses CardSubtype; Mutant has no constructor

**Nick Fury, Agent of S.H.I.E.L.D.** (`nickFuryAgentOfSHIELD`)

- `TraditionalCardDefinition.otherFace` — Second face of a transforming DFC (CardPart.alternative is Adventure-only)
- `SetPredicate.distinctNames` — Set-wide name constraints
- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)
- `CardAction.randomize` — Put on bottom in random order / pick a random card among
- `CardAction.transform` — Transform this permanent

**Night Nurse, Healer of Heroes** (`nightNurseHealerOfHeroes`)

- `TraditionalCardDefinition.CardSubtype.Doctor` — CardPart.subtype uses CardSubtype; Doctor has no constructor

**Ninja of the Hand** (`ninjaOfTheHand`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)
- `TraditionalCardDefinition.CardSubtype.Ninja` — CardPart.subtype uses CardSubtype; Ninja has no constructor

**Okoye, Dora Milaje Leader** (`okoyeDoraMilajeLeader`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Origin of the Avengers** (`originOfTheAvengers`)

- `TraditionalCardDefinition.sagaChapters` — Printed Saga chapters (roman numeral + actions); CardPart has no chapter
- `Trigger.sagaChapter` — When a lore counter is put / a (final) chapter ability resolves
- `CounterKind.lore` — Lore counters (putCounter only has plusOnePlusOne; CounterKind is used by CardAction)
- `Selector.manaValue` — Mana-value comparisons
- `Selector.inHand` — An object in a hand
- `TraditionalCardDefinition.CardSubtype.Saga` — CardPart.subtype uses CardSubtype; Saga has no constructor

**Panther Pounce** (`pantherPounce`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.investigate` — Investigate / create a Clue

**Pet Avengers** (`petAvengers`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `TraditionalCardDefinition.CardSubtype.Cat` — CardPart.subtype uses CardSubtype; Cat has no constructor
- `TraditionalCardDefinition.CardSubtype.Dog` — CardPart.subtype uses CardSubtype; Dog has no constructor
- `TraditionalCardDefinition.CardSubtype.Frog` — CardPart.subtype uses CardSubtype; Frog has no constructor

**Photon Blast Barrage** (`photonBlastBarrage`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `CardAction.copy` — Copy a permanent, spell, or ability


**Political Triumph** (`politicalTriumph`)

- `TraditionalCardDefinition.CardSubtype.Plan` — CardPart.subtype uses CardSubtype; Plan has no constructor

**Powerful Broker** (`powerfulBroker`)

- `CardAction.forEachCounterKind` — For each kind of counter on a selected object, give another of that kind


**Punishing Punch** (`punishingPunch`)

- `Condition.countAtLeast` — At least N objects match a selector (graveyard size, lore, quest counters, …)
- `ContinuousEffect.reduceCostByValue` — Reduce cost by a computed value (flying power, opp artifacts, source power, gy count) — reduceCost only takes a literal Cost list


**Quake, Agent of S.H.I.E.L.D.** (`quakeAgentOfSHIELD`)

- `TraditionalCardDefinition.CardSubtype.Inhuman` — CardPart.subtype uses CardSubtype; Inhuman has no constructor

**Quicksilver, Brash Blur** (`quicksilverBrashBlur`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn
- `CounterKind.named` — Named counters other than +1/+1 (hone, trample, quest, shadow, finality, …)
- `TraditionalCardDefinition.CardSubtype.Mutant` — CardPart.subtype uses CardSubtype; Mutant has no constructor

**Raft Security Officer** (`raftSecurityOfficer`)

- `Selector.powerAtMost` — Power at most N (only powerAtLeast exists)

**Rapid Rescue** (`rapidRescue`)

- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CardAction.mill` — Target player mills N cards

**Red Guardian, Super-Soldier** (`redGuardianSuperSoldier`)

- `Selector.damagedThisTurn` — Objects dealt damage this turn

**Red Hulk** (`redHulk`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Trigger.dealtDamage` — When the selected object is dealt damage (Enrage / watch-damage)
- `CardAction.eventAmount` — Use the amount of damage/life/cards from the triggering event ('that much')
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `Selector.countOf` — Numeric value derived from a count or characteristic
- `TraditionalCardDefinition.CardSubtype.Gamma` — CardPart.subtype uses CardSubtype; Gamma has no constructor
- `TraditionalCardDefinition.CardSubtype.Berserker` — CardPart.subtype uses CardSubtype; Berserker has no constructor

**Red Room Recruit** (`redRoomRecruit`)

- `CardAction.connive` — Connive

**Reptil, Dinomorpher** (`reptilDinomorpher`)

- `Selector.toughness` — Toughness comparisons / bind toughness as a number
- `ContinuousEffect.setPowerToughness` — Set base P/T to literal values (only from another object or a count exists)
- `ContinuousEffect.setTypes` — Set types/subtypes rather than only gain them

**Repulsor Blast** (`repulsorBlast`)

- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork / Crew)
- `Ability.keywordTeamwork` — Teamwork N as an optional additional cost
- `Condition.castWithTeamwork` — This spell was cast using teamwork


**Rewrite History** (`rewriteHistory`)

- `TraditionalCardDefinition.CardSubtype.Plan` — CardPart.subtype uses CardSubtype; Plan has no constructor

**Rick Jones, Destined Sidekick** (`rickJonesDestinedSidekick`)

- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CardAction.mill` — Target player mills N cards

**Robot Domination** (`robotDomination`)

- `Selector.color` — Objects of a color / colorless
- `TraditionalCardDefinition.CardSubtype.Plan` — CardPart.subtype uses CardSubtype; Plan has no constructor

**Ronin, Shadow Stalker** (`roninShadowStalker`)

- `Selector.attached` — Objects attached to a given object (inverse of hostOf)
- `Trigger.onceEachTurn` — Limit a trigger to once each turn
- `ContinuousEffect.restrictManaSpend` — Mana from an action may be spent only on matching events (current leftover is Elf-only)

**Roxxon Brutes** (`roxxonBrutes`)

- `TraditionalCardDefinition.CardSubtype.Berserker` — CardPart.subtype uses CardSubtype; Berserker has no constructor

**S.H.I.E.L.D. Deployment Drone** (`sHIELDDeploymentDrone`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**S.H.I.E.L.D. Flying Car** (`sHIELDFlyingCar`)

- `Cost.tapPowerTotal` — Tap creatures with total power N or more
- `Ability.keywordCrew` — Crew N
- `CardAction.exileThenReturn` — Exile then return at a later trigger (end step / leaves)

**S.H.I.E.L.D. Helicarrier** (`sHIELDHelicarrier`)

- `Cost.tapPowerTotal` — Tap creatures with total power N or more
- `Ability.keywordCrew` — Crew N
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `ContinuousEffect.setPowerToughness` — Set base P/T to literal values (only from another object or a count exists)
- `ContinuousEffect.setTypes` — Set types/subtypes rather than only gain them

**S.H.I.E.L.D. Spy Kit** (`sHIELDSpyKit`)

- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `Selector.attackingAlone` — A creature attacking alone
- `Trigger.attackAlone` — When the selected object attacks alone
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)

**Scientist Supreme of A.I.M.** (`scientistSupremeOfAIM`)

- `Trigger.onceEachTurn` — Limit a trigger to once each turn
- `CardAction.copy` — Copy a permanent, spell, or ability
- `TraditionalCardDefinition.CardSubtype.Scientist` — CardPart.subtype uses CardSubtype; Scientist has no constructor

**Secret Invasion** (`secretInvasion`)

- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield
- `Ability.keywordWard` — Ward with a cost (mana, discard-a-type, sacrifice legendary, poison, pay-or-discard)
- `Cost.wardNonmana` — Nonmana ward payments
- `CardAction.copy` — Copy a permanent, spell, or ability
- `ContinuousEffect.setPowerToughness` — Set base P/T to literal values (only from another object or a count exists)
- `ContinuousEffect.setTypes` — Set types/subtypes rather than only gain them

**Serpent Specialist** (`serpentSpecialist`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn
- `TraditionalCardDefinition.CardSubtype.Snake` — CardPart.subtype uses CardSubtype; Snake has no constructor

**Shang-Chi, Master of Kung Fu** (`shangChiMasterOfKungFu`)

- `ContinuousEffect.restrictManaSpend` — Mana from an action may be spent only on matching events (current leftover is Elf-only)

**She-Hulk, Jade Defender** (`sheHulkJadeDefender`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn
- `TraditionalCardDefinition.CardSubtype.Gamma` — CardPart.subtype uses CardSubtype; Gamma has no constructor

**Shuri, Wakandan Inventor** (`shuriWakandanInventor`)

- `CardAction.copy` — Copy a permanent, spell, or ability
- `ContinuousEffect.setPowerToughness` — Set base P/T to literal values (only from another object or a count exists)
- `ContinuousEffect.setTypes` — Set types/subtypes rather than only gain them
- `TraditionalCardDefinition.CardSubtype.Artificer` — CardPart.subtype uses CardSubtype; Artificer has no constructor

**Speed, Young Avenger** (`speedYoungAvenger`)

- `TraditionalCardDefinition.CardSubtype.Mutant` — CardPart.subtype uses CardSubtype; Mutant has no constructor

**Speedball, New Warrior** (`speedballNewWarrior`)

- `Trigger.becomeTarget` — When the selected object becomes the target of a spell or ability
- `CardAction.changeTargets` — Choose new targets for another spell or ability


**Spider-Man, To the Rescue** (`spiderManToTheRescue`)

- `Trigger.whenYouDo` — Nested delayed trigger after an optional action ('when you do')


**Spider-Woman, Secret Agent** (`spiderWomanSecretAgent`)

- `ContinuousEffect.skipsUntap` — Selected permanents don't untap during the untap step
- `ContinuousEffect.forbidUntapWhileYouControl` — Can't become untapped for as long as you control this


**Stark Industries Executive** (`starkIndustriesExecutive`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Stature, Size Shifter** (`statureSizeShifter`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Cost.manaX` — Pay {X} / {X}{X} (ManaSymbol list has no X variable in Cost.mana as a bound value for later actions)
- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn

**Storm, Windrider** (`stormWindrider`)

- `TraditionalCardDefinition.CardSubtype.Mutant` — CardPart.subtype uses CardSubtype; Mutant has no constructor

**Super Intelligence** (`superIntelligence`)

- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player

**Super Strength** (`superStrength`)

- `Trigger.becomeTarget` — When the selected object becomes the target of a spell or ability
- `Ability.keywordWard` — Ward with a cost (mana, discard-a-type, sacrifice legendary, poison, pay-or-discard)
- `Cost.wardNonmana` — Nonmana ward payments

**Super Villain Lockup** (`superVillainLockup`)

- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield
- `Ability.linkedExile` — Paired exile-until-leaves (enter trigger + leave trigger sharing exiled objects)
- `CardAction.returnExiled` — Return objects exiled by a linked action

**Super-Adaptoid** (`superAdaptoid`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `ContinuousEffect.addPowerToughnessPer` — Pump / set PT from a count other than setPowerToughnessEqualToCount's lands-you-control leftover
- `Selector.countOf` — Numeric value derived from a count or characteristic
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed

**Super-Skrull** (`superSkrull`)

- `Selector.color` — Objects of a color / colorless
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `TraditionalCardDefinition.CardSubtype.Skrull` — CardPart.subtype uses CardSubtype; Skrull has no constructor

**Super-Soldier Serum** (`superSoldierSerum`)

- `ContinuousEffect.gainSupertype` — Gain a supertype in addition to other types (legendary)
- `Range.anyNumber` — Any number (range 0 ∞); Range.range needs a finite Nat hi


**Surveillance Room** (`surveillanceRoom`)

- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CardAction.surveil` — Surveil N
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)

**Swordsman, Sharp Scoundrel** (`swordsmanSharpScoundrel`)

- `CardAction.connive` — Connive

**Taskmaster, Mercenary Mimic** (`taskmasterMercenaryMimic`)

- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player
- `CardAction.copy` — Copy a permanent, spell, or ability
- `ContinuousEffect.setPowerToughness` — Set base P/T to literal values (only from another object or a count exists)
- `ContinuousEffect.setTypes` — Set types/subtypes rather than only gain them
- `TraditionalCardDefinition.CardSubtype.Mercenary` — CardPart.subtype uses CardSubtype; Mercenary has no constructor

**Team Tactics** (`teamTactics`)

- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork / Crew)
- `Ability.keywordTeamwork` — Teamwork N as an optional additional cost
- `Condition.castWithTeamwork` — This spell was cast using teamwork

**Thanos, the Mad Titan** (`thanosTheMadTitan`)

- `CardAction.chooseOddEven` — Choose odd or even
- `Condition.manaValueParity` — Mana value is odd/even
- `Selector.manaValue` — Mana-value comparisons
- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn
- `TraditionalCardDefinition.CardSubtype.Eternal` — CardPart.subtype uses CardSubtype; Eternal has no constructor

**The Astonishing Ant-Man** (`theAstonishingAntMan`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `CardAction.removeCounter` — Remove counters from the selected object
- `TraditionalCardDefinition.CardSubtype.Scientist` — CardPart.subtype uses CardSubtype; Scientist has no constructor

**The Coming of Galactus** (`theComingOfGalactus`)

- `TraditionalCardDefinition.sagaChapters` — Printed Saga chapters (roman numeral + actions); CardPart has no chapter
- `Trigger.sagaChapter` — When a lore counter is put / a (final) chapter ability resolves
- `CounterKind.lore` — Lore counters (putCounter only has plusOnePlusOne; CounterKind is used by CardAction)
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)
- `TraditionalCardDefinition.CardSubtype.Saga` — CardPart.subtype uses CardSubtype; Saga has no constructor

**The Incredible Hulk** (`theIncredibleHulk`)

- `Trigger.dealtDamage` — When the selected object is dealt damage (Enrage / watch-damage)
- `CardAction.eventAmount` — Use the amount of damage/life/cards from the triggering event ('that much')
- `CardAction.extraCombat` — An additional combat phase; typically with untap attackers
- `TraditionalCardDefinition.CardSubtype.Gamma` — CardPart.subtype uses CardSubtype; Gamma has no constructor
- `TraditionalCardDefinition.CardSubtype.Berserker` — CardPart.subtype uses CardSubtype; Berserker has no constructor

**The Invincible Iron Man** (`theInvincibleIronMan`)

- `Selector.inHand` — An object in a hand
- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player

**The Kingpin of Crime** (`theKingpinOfCrime`)

- `Selector.toughness` — Toughness comparisons / bind toughness as a number
- `Ability.keywordExtort` — Extort
- `CardAction.payThen` — You may pay a cost. If you do, perform actions (resolution-time optional payment, not an activated cost)
- `CardAction.eventAmount` — Bind/use an amount from a previous action or trigger (that much, excess, sacrificed power)
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)

**The Masters of Evil** (`theMastersOfEvil`)

- `TraditionalCardDefinition.CardSubtype.Plan` — CardPart.subtype uses CardSubtype; Plan has no constructor


**The Mind Stone** (`theMindStone`)

- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player
- `CardAction.exileThenReturn` — Exile then return at a later trigger (end step / leaves)
- `TraditionalCardDefinition.CardSubtype.Infinity` — CardPart.subtype uses CardSubtype; Infinity has no constructor
- `TraditionalCardDefinition.CardSubtype.Stone` — CardPart.subtype uses CardSubtype; Stone has no constructor

**The Ruinous Wrecking Crew** (`theRuinousWreckingCrew`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)

**The Scarlet Witch** (`theScarletWitch`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.manaValue` — Mana-value comparisons
- `Cost.manaX` — Pay {X} / {X}{X} (ManaSymbol list has no X variable in Cost.mana as a bound value for later actions)
- `TraditionalCardDefinition.CardSubtype.Mutant` — CardPart.subtype uses CardSubtype; Mutant has no constructor
- `TraditionalCardDefinition.CardSubtype.Warlock` — CardPart.subtype uses CardSubtype; Warlock has no constructor

**The Sensational She-Hulk** (`theSensationalSheHulk`)

- `Trigger.dealtDamage` — When the selected object is dealt damage (Enrage / watch-damage)
- `CardAction.eventAmount` — Use the amount of damage/life/cards from the triggering event ('that much')
- `Trigger.onceEachTurn` — Limit a trigger to once each turn
- `ContinuousEffect.forbidCast` — Players matching a selector can't cast spells matching a selector
- `TraditionalCardDefinition.CardSubtype.Gamma` — CardPart.subtype uses CardSubtype; Gamma has no constructor

**The Sentry, Golden Guardian** (`theSentryGoldenGuardian`)

- `ContinuousEffect.forbidAttack` — Can't attack / attacks-if-able (forbid exists for Trigger; need an attack event plus a restriction combinator)
- `Condition.controlCount` — Controller controls N or more matching objects

**The Serpent Society** (`theSerpentSociety`)

- `Ability.keywordWard` — Ward with a cost (mana, discard-a-type, sacrifice legendary, poison, pay-or-discard)
- `Cost.wardNonmana` — Nonmana ward payments
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)
- `TraditionalCardDefinition.CardSubtype.Snake` — CardPart.subtype uses CardSubtype; Snake has no constructor

**The Super Hero Civil War** (`theSuperHeroCivilWar`)

- `TraditionalCardDefinition.sagaChapters` — Printed Saga chapters (roman numeral + actions); CardPart has no chapter
- `Trigger.sagaChapter` — When a lore counter is put / a (final) chapter ability resolves
- `CounterKind.lore` — Lore counters (putCounter only has plusOnePlusOne; CounterKind is used by CardAction)
- `Selector.manaValue` — Mana-value comparisons
- `CardAction.gainControl` — Gain control of selected objects
- `TraditionalCardDefinition.CardSubtype.Saga` — CardPart.subtype uses CardSubtype; Saga has no constructor

**The Ten Rings** (`theTenRings`)

- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player
- `ContinuousEffect.handSize` — Set / remove maximum hand size


**The Unbeatable Squirrel Girl** (`theUnbeatableSquirrelGirl`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `TraditionalCardDefinition.CardSubtype.Squirrel` — CardPart.subtype uses CardSubtype; Squirrel has no constructor

**The Vision** (`theVision`)

- `Condition.modeNotChosenThisTurn` — Choose a mode that hasn't been chosen this turn
- `CardAction.chooseModes` — Modal selection beyond exclusive chooseMode (one-or-both, choose-two-if, choose-both-if-teamwork)


**The Wondrous Wasp** (`theWondrousWasp`)

- `ContinuousEffect.loseAbilities` — Selected object loses all abilities


**Thor, God of Thunder** (`thorGodOfThunder`)

- `Selector.manaValue` — Mana-value comparisons
- `CardAction.repeatN` — Repeat an action / deal damage / draw / put counters X times where X is computed
- `Selector.countOf` — Numeric value derived from a count or characteristic

**Thunderbolts Conspiracy** (`thunderboltsConspiracy`)

- `ContinuousEffect.replace` — replace already exists; need a would-die / would-go-to-gy trigger which putToGraveyard covers — exile-instead is expressible if replace actions can exile (compiler may not)
- `CounterKind.named` — Named counters other than +1/+1 (hone, trample, quest, shadow, finality, …)

**Tigra, Feline Fury** (`tigraFelineFury`)

- `Trigger.gainLife` — Whenever the selected player gains life
- `TraditionalCardDefinition.CardSubtype.Cat` — CardPart.subtype uses CardSubtype; Cat has no constructor

**Titania, Rugged Rumbler** (`titaniaRuggedRumbler`)

- `Trigger.becomeTarget` — When the selected object becomes the target of a spell or ability
- `Selector.inHand` — A card in hand for Cost.discard
- `Ability.keywordWard` — Ward with a cost (mana, discard-a-type, sacrifice legendary, poison, pay-or-discard)
- `Cost.wardNonmana` — Nonmana ward payments
- `Cost.or` — Cost.or exists; need discard-a-card (inHand) OR pay generic

**Tony Stark** (`tonyStark`)

- `TraditionalCardDefinition.otherFace` — Second face of a transforming DFC (CardPart.alternative is Adventure-only)
- `SetPredicate.distinctNames` — Set-wide name constraints
- `Selector.topNOfLibrary` — The top N cards of a library (only topOfLibrary for N=1 exists)
- `CardAction.lookAt` — Look at / reveal the top N cards (reveal exists for selected objects, not a library slice)
- `CardAction.randomize` — Put on bottom in random order / pick a random card among
- `CardAction.transform` — Transform this permanent
- `TraditionalCardDefinition.CardSubtype.Artificer` — CardPart.subtype uses CardSubtype; Artificer has no constructor

**Too Evil to Stay Dead** (`tooEvilToStayDead`)

- `Selector.manaValue` — Mana-value comparisons
- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork / Crew)
- `Ability.keywordTeamwork` — Teamwork N as an optional additional cost
- `Condition.castWithTeamwork` — This spell was cast using teamwork

**Training Regimen** (`trainingRegimen`)

- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player

**Trickster's Stratagem** (`tricksterSStratagem`)

- `CardAction.connive` — Connive

**U.S.Agent, John Walker** (`uSAgentJohnWalker`)

- `Selector.color` — Objects of a color / colorless
- `Selector.named` — Objects with a given name
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Ultron Drone** (`ultronDrone`)

- `Selector.color` — Objects of a color / colorless
- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn
- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)

**Ultron, Artificial Malevolence** (`ultronArtificialMalevolence`)

- `CardAction.createToken` — Create n tokens of a described kind
- `TraditionalCardDefinition.tokenDescription` — Inline token characteristics (or a TokenKind reference)
- `CardAction.payThen` — You may pay a cost. If you do, perform actions (resolution-time optional payment, not an activated cost)
- `CardAction.copy` — Copy a permanent, spell, or ability
- `ContinuousEffect.setPowerToughness` — Set base P/T to literal values (only from another object or a count exists)
- `ContinuousEffect.setTypes` — Set types/subtypes rather than only gain them

**Undercover Skrull** (`undercoverSkrull`)

- `TraditionalCardDefinition.CardSubtype.Skrull` — CardPart.subtype uses CardSubtype; Skrull has no constructor

**Unliving Legionnaire** (`unlivingLegionnaire`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn
- `TraditionalCardDefinition.CardSubtype.Vampire` — CardPart.subtype uses CardSubtype; Vampire has no constructor

**Villainous Hideout** (`villainousHideout`)

- `Selector.inHand` — A card in hand for Cost.discard
- `CardAction.connive` — Connive
- `ContinuousEffect.restrictManaSpend` — Mana from an action may be spent only on matching events (current leftover is Elf-only)

**Vision Quest** (`visionQuest`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.manaValue` — Mana-value comparisons


**Viv Vision, Teen Synthezoid** (`vivVisionTeenSynthezoid`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn

**Volcanic Villain** (`volcanicVillain`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn


**War Machine, Legacy of Iron** (`warMachineLegacyOfIron`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Trigger.beginStep` — At the beginning of a named phase/step (upkeep, combat, end, first main) for a player

**We Say Thee Nay!** (`weSayTheeNay`)

- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork / Crew)
- `Ability.keywordTeamwork` — Teamwork N as an optional additional cost
- `Condition.castWithTeamwork` — This spell was cast using teamwork
- `TraditionalCardDefinition.CardSubtype.Arcane` — CardPart.subtype uses CardSubtype; Arcane has no constructor

**Web Up** (`webUp`)

- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield
- `Ability.linkedExile` — Paired exile-until-leaves (enter trigger + leave trigger sharing exiled objects)
- `CardAction.returnExiled` — Return objects exiled by a linked action

**Whiplash, Vengeful Engineer** (`whiplashVengefulEngineer`)

- `Range.computed` — Count bounds that are a computed number (X, that many, a count/characteristic) rather than literal Nat
- `Selector.attached` — Objects attached to a given object (inverse of hostOf)
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)
- `TraditionalCardDefinition.CardSubtype.Artificer` — CardPart.subtype uses CardSubtype; Artificer has no constructor

**White Tiger, Ava Ayala** (`whiteTigerAvaAyala`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn


**Wiccan, Rising Magician** (`wiccanRisingMagician`)

- `CardAction.exileThenReturn` — Exile then return at a later trigger (end step / leaves)
- `TraditionalCardDefinition.CardSubtype.Mutant` — CardPart.subtype uses CardSubtype; Mutant has no constructor
- `TraditionalCardDefinition.CardSubtype.Warlock` — CardPart.subtype uses CardSubtype; Warlock has no constructor

**Widow's Bite** (`widowSBite`)

- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork / Crew)
- `Ability.keywordTeamwork` — Teamwork N as an optional additional cost
- `Condition.castWithTeamwork` — This spell was cast using teamwork
- `CardAction.chooseModes` — Modal selection beyond exclusive chooseMode (one-or-both, choose-two-if, choose-both-if-teamwork)

**Winter Soldier, Icy Assassin** (`winterSoldierIcyAssassin`)

- `Selector.attached` — Objects attached to a given object (inverse of hostOf)
- `Ability.activateFromZone` — Activated ability that functions in the graveyard (or another non-battlefield zone)
- `ContinuousEffect.replace` — replace already exists; need a would-die / would-go-to-gy trigger which putToGraveyard covers — exile-instead is expressible if replace actions can exile (compiler may not)
- `ContinuousEffect.addPowerToughnessPer` — Pump / set PT from a count other than setPowerToughnessEqualToCount's lands-you-control leftover
- `Selector.countOf` — Numeric value derived from a count or characteristic
- `CounterKind.named` — Named counters other than +1/+1 (hone, trample, quest, shadow, finality, …)
- `TraditionalCardDefinition.CardSubtype.Assassin` — CardPart.subtype uses CardSubtype; Assassin has no constructor

**Wolverine, Fierce Fighter** (`wolverineFierceFighter`)

- `TraditionalCardDefinition.CardSubtype.Mutant` — CardPart.subtype uses CardSubtype; Mutant has no constructor
- `TraditionalCardDefinition.CardSubtype.Berserker` — CardPart.subtype uses CardSubtype; Berserker has no constructor

**Wonder Man, Hollywood Hero** (`wonderManHollywoodHero`)

- `Condition.enteredThisTurn` — The selected object entered this turn
- `Ability.activatedOnce` — Activated ability limited to once (power-up); optionally cheaper if the source entered this turn
- `Condition.sourceEnteredThisTurn` — The source entered this turn
- `ContinuousEffect.extraTrigger` — Matching triggered abilities trigger an additional time
- `TraditionalCardDefinition.CardSubtype.Performer` — CardPart.subtype uses CardSubtype; Performer has no constructor

**World War Hulk** (`worldWarHulk`)

- `TraditionalCardDefinition.sagaChapters` — Printed Saga chapters (roman numeral + actions); CardPart has no chapter
- `Trigger.sagaChapter` — When a lore counter is put / a (final) chapter ability resolves
- `CounterKind.lore` — Lore counters (putCounter only has plusOnePlusOne; CounterKind is used by CardAction)
- `TraditionalCardDefinition.CardSubtype.Saga` — CardPart.subtype uses CardSubtype; Saga has no constructor

**Worlds Within Worlds** (`worldsWithinWorlds`)

- `Selector.inHand` — An object in a hand
- `Selector.eachPlayer` — All players / all opponents as a set to iterate (forEachVariable exists but there is no all-players selector)
- `Range.anyNumber` — Any number (range 0 ∞); Range.range needs a finite Nat hi


**Dark Fortress** (`darkFortress`)

- `Condition.or` — Activate only if this land entered this turn or you control a basic land
- `Condition.enteredThisTurn` — This land entered this turn

**Gathering Place** (`gatheringPlace`)

- `Condition.or` — Activate only if this land entered this turn or you control a basic land
- `Condition.enteredThisTurn` — This land entered this turn

**Gleaming Bastion** (`gleamingBastion`)

- `Condition.or` — Activate only if this land entered this turn or you control a basic land
- `Condition.enteredThisTurn` — This land entered this turn

**Hidden Lair** (`hiddenLair`)

- `Condition.or` — Activate only if this land entered this turn or you control a basic land
- `Condition.enteredThisTurn` — This land entered this turn

**Training Compound** (`trainingCompound`)

- `Condition.or` — Activate only if this land entered this turn or you control a basic land
- `Condition.enteredThisTurn` — This land entered this turn

## Method notes

- A card is “remaining” when its catalog `def` is a `CardDef` whose body is
  not a `TraditionalCardDefinition.card […]` (and is not a `fooCard` wrapper
  around such a definition).
- Tags come from Oracle text plus modeled fields (`triggeredAbilities`,
  `staticAbilities`, `Effect.*`, CardDef flags such as `teamwork`, `otherFace`,
  `saga`, `crew`, `ward`, …).
- Reminder text in parentheses can still mention tokens (Amass, Recruit).
  Token-creation tags therefore include those ability words.
- `toCardDef` compilation gaps are out of scope except where the types
  themselves cannot name the ability (for example `Condition` has `and` but
  not `or` / `not`).
