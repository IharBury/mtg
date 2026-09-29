# TraditionalCardDefinition conversion gaps

This note records what is missing from the part-based printed-card types in
`Mtg/Engine/Card/Definition.lean` and `Mtg/Engine/Card/Keywords.lean` in
order to convert every **currently supported catalog card** that is not yet
written as a `TraditionalCardDefinition`.

**213** catalog cards are still `CardDef` helpers. **200**
of them need at least one missing constructor listed under
[Missing constructors by type](#missing-constructors-by-type). **13** lost
their last tag (named counters, `CardAction.removeCounter`, or
enters-with-counters) and are not converted yet (see
[Tags now spelled](#tags-now-spelled-not-yet-converted)).
Compiler leftovers in `toCardDef` / `CardAction.compile` are mentioned
when a constructor already exists but cannot express the printed ability
without a new constructor.

## Scope

`Oracle.supportedCatalogCards` is the core vanilla cards plus
`Catalog.hobbitCards`, `Catalog.hobbitEternalCards`, and `Catalog.mshCards`.
Counts exclude the basic lands that `hobbitCards` shares with the core
catalog.

| Set | Catalog cards | `TraditionalCardDefinition` | Remaining `CardDef` | Remaining with a constructor gap |
| --- | ---: | ---: | ---: | ---: |
| The Hobbit (HOB) | 188 | 150 | 38 | 35 |
| The Hobbit Eternal (HOC) | 117 | 67 | 50 | 48 |
| Marvel Super Heroes (MSH) | 281 | 156 | 125 | 117 |
| **Total** | **586** | **373** | **213** | **200** |

All 373 `TraditionalCardDefinition`s (150 HOB, 67 HOC, 156 MSH,
including Giant Growth) spell only their printed characteristics as parts
and read the rest of their Oracle text with `parseOracleParts`
(`Mtg/Engine/Card/OracleParse.lean`). A `#guard` next to each one pins the
parsed definition. The Sackville-Bagginses reads “Whenever you sacrifice a
token” as sacrificing a token permanent you control, and The Thing, Ben Grimm
reads “Whenever one or more Heroes you control deal damage to a player” as
those Heroes dealing damage to a player at the same time.

Evidence for each remaining card is its catalog definition (Oracle text plus
modeled `CardDef` fields, triggered/static/activated constructors, and
`Effect` names) compared with the current constructors of `Range`,
`SetPredicate`, `Value`, `Selector`, `Trigger`, `Cost`, `Condition`,
`Ability`, `ContinuousEffect`, `CardAction`, and `TraditionalCardDefinition`
(including `CardPart`).

`Keyword` is not in the requested list. It still blocks because
`Ability.keyword` and `CardAction.keyword` are indexed by it. Missing
`Keyword` constructors are listed under `Ability` / `CardAction`.
`CounterKind` has a constructor for every named counter in the supported
catalog, so it no longer blocks a conversion. `CardSubtype` includes Wall,
Minion, and Elder. Plan enchantments stay blocked by put-counter triggers,
not missing subtypes.

## Current constructors (inventory)

From `Mtg/Engine/Card/Keywords.lean` and `Mtg/Engine/Card/Definition.lean`:

- **Range** — `range lo hi` (`Value` bounds), `any` (0 unbounded), `from n` (`Value` lower bound, unbounded high).
- **SetPredicate** — `shareCardType`, `countAtLeast`.
- **Value** — `nat`, `int`, `x`, `greatestManaValue`, `greatestToughness`,
  `greatestPower`, `count`, `totalPower`, `product`, `variable` (recorded by
  `CardAction.defineValueVariable`).
- **Keyword** — `flash`, `haste`, `vigilance`, `flying`, `menace`, `hexproof`,
  `indestructible`, `reach`, `trample`, `deathtouch`, `defender`, `lifelink`,
  `firstStrike`, `islandwalk`, `storied`, `doubleStrike`, `prowess`, `ascend`,
  `shadow`, `changeling`, `equip`, `enchant`, `typecycling`, `recruit`,
  `amass`, `connive`, `chapter`, `flashback`, `ward`, `crew`, `teamwork`,
  `improvise`, `kicker`, `affinity`, `boast`, `cascade`, `extort`, `sneak`,
  `gift` (`Gift`: a Food, a card, a tapped Fish, an extra turn, a Treasure, an Octopus; CR 702.174d–i).
- **CounterKind** — `plusOnePlusOne`, and one constructor per other printed
  counter in the supported catalog: `burden`, `deathtouch`, `doubleStrike`,
  `finality`, `firstStrike`, `flying`, `haste`, `hone`, `hope`,
  `indestructible`, `influence`, `invasion`, `lifelink`, `menace`, `plan`,
  `quest`, `reach`, `shadow`, `shield`, `stun`, `trample`, `vigilance`.
  Lore counters are Saga chapters. Poison counters as a Ward cost stay
  `Cost.getPoisonCounters`.
- **Selector** — `this`, `source`, `controller`, `caster` (the player who would cast this spell), `target` / `targets` / `targetSet` (unique numbers per card), `not`, `targetReference`, `selected`, `intersection`, `all`,
  `cardType`, `union`, `permanent`, `controlled`, `tapped`, `keyword`,
  `keywordAbility`, `powerAtLeast`, `powerAtMost`, `hasCounter`, `subtype`,
  `spell`, `ability`, `abilityWithId`, `permanentSpell`, `hasTarget`,
  `isTargetOf`, `player`, `opponent`, `owner`, `attacking`, `blocking`,
  `token`, `wasObjectOfAction`, `wasArgumentOfTrigger`, `replacingObject`,
  `wasCreatedByAction`, `hostOf`, `inGraveyard`, `wasObjectSince`,
  `inLibrary`, `inHand`, `inExile`, `supertype`, `variable`, `topOfLibrary`
  (whose library, how many cards), `hasCreatureTypeChosenByAction` (the
  creature type chosen by a numbered `CardAction.chooseCreatureType`),
  `manaValueAtMost` (mana value at most a `Value`).
- **Trigger** — `endOfGame`, `endOfTurn`, `endOfPlayerTurn`,
  `combatStart` (player whose turn it is), `upkeep`, `endStep`,
  `precombatMainPhase`, `turnStart`, `gameStart`, `attack`, `enter`, `draw`,
  `ordinal`, `combatDamage`, `damage`, `damageSimultaneously` (who deals
  damage, who is dealt damage, at the same time), `putToGraveyard`,
  `leaveGraveyard`, `returnToHand`, `discard`, `putCountersSimultaneously`,
  `block`, `die`, `dieSimultaneously`, `sacrifice` (the permanents sacrificed),
  `attackSimultaneously` (who attacks, who is attacked),
  `abilityWithIdActivated`, `actionWithId`, `triggerId`, `modeWithIdChosen`,
  `spendManaCreatedByAction`, `spendManaFrom`, `castSpell`,
  `castSpellFromGraveyard`, `counter`, `activateAbility`, `target` (a spell or
  ability targets an object), `sequence`, `not`, `or`.
- **Cost** — `mana` (including `ManaSymbol.x`), `life`, `sacrifice` (every selected permanent),
  `sacrificeCount` (that many matching permanents), `tapSymbol`,
  `discard` (what to discard), `or`.
- **Condition** — `any`, `targetsIncludeAny`, `anySubtype`, `didNotHappen`,
  `happened`, `timeToCastSorcery`, `turn`, `enduringStory`, `and`, `not`,
  `less`, `lessOrEqual`, `greater`, `greaterOrEqual`, `equal`,
  `giftPromised`.
- **CardState** — `tapped`, `attacking` (enters attacking), `controlled` (who controls as the permanent enters), `attachedTo`.
- **Ability** — `keyword`, `keywordWithCost`, `keywordWithSubtypeAndCost`,
  `keywordWithTarget`, `keywordWithEffect`, `activated`, `activatedIf`,
  `activatedWithStaticIf` (with a static effect of that ability, such as its
  own cost reduction), `graveyardActivatedIf`, `abilityId`, `triggered`,
  `triggeredWhile` (condition checked when the trigger event occurs, not on resolution),
  `static`, `stackStatic`, `everywhereStatic` (functions in every zone, including before the card is put onto the stack).
- **ContinuousEffect** — `gainAbility`, `if`, `reduceCost`, `reduceCostWithX`
  (substitutes `{X}` with a `Value`), `additionalCost`, `alternativeCost`,
  `replace`, `forbid`, `canCastWithoutPayingManaCost`, `canPlay`,
  `setBasePower`, `setBaseToughness`, `gainType`, `gainSubtype`,
  `gainAllSubtypes`, `setPower`, `setToughness`, `addPower`, `addToughness`,
  `increaseLandPlayLimit`, `canBeCastAsThoughWithFlashIf` (the spell can be
  cast as though it had flash when a condition holds; `you` is
  `Selector.caster`; the spell does not gain flash), `doesntUntap`,
  `cantAttackUnlessPays`.
- **CardAction** — `continuous`, `tap`, `untap`, `dealDamage`, `divideDamage`,
  `draw`, `scry`, `sequence`, `if`, `ifElse`, `optional`, `attach`,
  `chooseUniqueModes`, `chooseModeRestricted`, `counter`, `preventable`,
  `optionalPayFor`, `discard`, `putCounter` (a `Value` count), `removeCounter`,
  `exile`, `exileFaceDown`,
  `exchangeControl`, `destroy`, `gainLife`, `playerSelectAction`,
  `putOnTopOfLibrary`, `putOnBottomOfLibrary`, `putIntoLibraryFromTop`,
  `actionId`, `loseLife`, `sacrifice`, `returnToHand`, `putOntoBattlefield`,
  `putOntoBattlefieldInState`, `searchLibraryThenShuffle`,
  `holdOutInLibrary`, `defineSelectorVariable`, `defineValueVariable`,
  `forEachVariable`, `reveal`, `dealDamageEqualToPower`, `fight`,
  `addManaOfOneColor`, `addManaInAnyCombination`, `addMana`, `keyword`,
  `createTokens`, `mill`, `surveil`, `copyWithNewTargets`,
  `keepReplacedAction`, `healAllDamage`, `shuffleIntoOwnersLibrary`,
  `lookAt`, `putOnLibraryBottomInRandomOrder`, `chooseCreatureType` (the
  selected player chooses a creature type).
- **TraditionalCardDefinition** — `card : List CardPart`, with `CardPart`
  `name`, `manaCost`, `type`, `supertype`, `subtype`, `colorIndicator`,
  `power`, `toughness`, `ability`, `alternative` (Adventure face), `actions`.

Converted catalog cards (Bofur, Lightning Bolt, Wood Elves, Rogue's Passage,
Gundabad Opportunist, Elvish Mystic, Guttersnipe, Fisk Tower, Patient
Instructor, Goblin-town Flunkies, …) already use that inventory. Remaining
cards need the constructors below. `CardAction.keyword` compiles keyword
actions such as recruit and amass. `CardAction.createTokens` compiles token
creation from a selector, count, `CardPart` characteristics, and optional
entering states (tapped, attacking).
`CardAction.ifElse` compiles an “if … instead …” replacement (Andúril’s
legendary Spirits). `CardAction.mill` compiles milling a selected player
that many cards (and mill-then-put sequences through leftovers).
`CardAction.surveil` compiles the selected player surveilling that many
cards (enter triggers, destroy-then-surveil, and Redwing token creation
through leftovers).
`SetPredicate.countAtLeast` is the set-wide size of a simultaneous event
(Landroval’s two or more creatures attacking a player).
`ContinuousEffect.addPower` of `Value.count` compiles other-subtype +1/+0 for
each artifact token you control (Thorin). A factor of one is the count.
Zero toughness is omitted.
Aragorn and Arwen’s leftover is +1/+1 on each other creature you control and
1 life per those creatures (`forEachVariable`), not a flat 1 life.
`CardAction.chooseModeRestricted` is who chooses and, for each mode, an ID,
when it is allowed, and its actions (Galadriel: you, unchosen this turn by
any player). `chooseUniqueModes` does not leftover to that triggered
ability. `Trigger.modeWithIdChosen` of only you stays uncompiled.
`Selector.wasObjectSince` is “the object of this event since that event”
(Night Nurse: `putToGraveyard` since `turnStart`). `Condition.greaterOrEqual` of
`Value.count` is an object count (Arnim Zola’s two or more creature cards in the graveyard). `Trigger.discard`
is “whenever you discard” (Moonstone). The leftover exiles `Selector.wasArgumentOfTrigger`
of that discard from the graveyard (that discarded card); any graveyard card stays uncompiled.
`Selector.hasTarget` is “has a target matching …” (Fin Fang Foom: artifact or
land). `CardAction.copyWithNewTargets` is who copies and what is copied (you,
that spell). Intervening `targetsIncludeAny` without copy stays uncompiled.
Justice’s bounce-watch leftover is `Trigger.returnToHand` of
another nonland you control (tokens included). Put-to-graveyard leftovers stay
uncompiled.
`CardAction.optionalPayFor` is who may pay, what cost, and what happens if
paid (Speed: you, {1}, haste-except-haste). Bullseye’s nonland discard is
`Cost.discard` (ETB via `optionalPayFor`, activated via `Cost.or`). `CardAction.fight` is Wolverine’s ETB.
`CardAction.healAllDamage` heals all marked damage on the selected object.
`CardAction.keepReplacedAction` performs the action being replaced. Wolverine’s leftover
is `replace` of any damage to this with `healAllDamage` of this then `keepReplacedAction`.
Empty replacement, combat-only, keep without heal, heal without keep, or keep then
heal stay uncompiled. `Trigger.putCountersSimultaneously` is
one or more counters of a kind on the selected objects at the same time
(Beast: +1/+1 this turn). Storm’s leftover is `hasTarget` of a creature on the spell you cast, then
flying on creatures that are `isTargetOf` argument 1 of that cast (`wasArgumentOfTrigger`).
Treating the spell as those creatures stays uncompiled. Intervening
`targetsIncludeAny` or flying on all creatures stays uncompiled. Storm’s
flying restriction is
`forbid` of attack-or-block, not attack alone.
`Selector.keywordAbility` is a keyword ability of that keyword (Dwarven
Mauler: Equip abilities you activate that `hasTarget` this). Using
`keyword`, omitting the target, or omitting you-activate stays uncompiled.
`Keyword.chapter` is a Saga chapter number. `Ability.keywordWithEffect` is
that keyword printed with resolution actions. Armor Wars leftovers are
`optional` draw-for-each-artifact then each opponent draws
(`mayDrawPerArtifactOppsDraw`); `reduceCost` of artifact spells you cast
until end of turn (`artifactSpellsCostLessThisTurn`); and
`CardAction.dealDamage` of this to a target opponent for
`Value.greatestManaValue` of artifacts you control
(`chapterDealXDamageToTargetOpponentGreatestArtifactMv`). Non-optional draw,
creature-not-artifact, missing opponent draw, each-player draw, lasting
(not this-turn) reduction, creature spells, artifact permanents, target
player, greatest mana value among creatures, or literal `Value.nat` stay
uncompiled. Uncompiled chapter actions produce no `SagaDef`.
`Trigger.leaveGraveyard` is whenever a matching card leaves a graveyard
(Along the Crooked Way: creature cards in your graveyard, then amass
Goblins). Other leave-graveyard selectors stay uncompiled. Enter return of
target creature card from your graveyard leftover to
`onEnterReturnCreatureFromGyToHand`. Goblins and Orcs you control gaining
menace leftover to `Effect.subtypesGainMenace`; creatures you control
without a subtype still leftover to `teamGain`. Flying, opponent-controlled,
or up-to-one graveyard return stay uncompiled as those leftovers.
`ContinuousEffect.gainAllSubtypes` is who gains all subtypes of that type
(Undercover Skrull: this, creature). Pump-only leftovers compile to
`getsIfGyCreatureCards`, not all creature types. `gainSubtype` of one subtype
stays uncompiled as all-types.
`CardSubtype` constructors from the previous change, plus leftovers in
`toCardDef`, compile search-two-basics, Plan-card search, gy-creature
statics, Alliance modes, second-draw +1/+1 on a target, and the other
printed abilities of the 21 subtype-unlocked catalog cards.

## Former gaps that current constructors cover

An earlier revision tagged these gaps on the remaining cards. The listed
constructors now spell them, so the tags are gone from the lists below.

| Former gap | Spelled with |
| --- | --- |
| `Selector.topNOfLibrary` | `Selector.topOfLibrary` of a player and a `Value` count |
| `Selector.countOf`, `CardAction.repeatN`, `CardAction.addManaPer` | `Value.count`, `totalPower`, `greatestPower`, `greatestToughness`, `greatestManaValue`, `product`; `draw`, `dealDamage`, `gainLife`, `loseLife`, `mill`, `createTokens`, `addManaOfOneColor`, and `Keyword.amass` take a `Value` |
| `Selector.inHand`, `inExile`, `powerAtMost`, `hasCounter` | The `Selector` constructors of those names |
| `Selector.eachPlayer` | `Selector.player` / `Selector.opponent`, with `forEachVariable` |
| `Selector.named`, colorless tokens under `Selector.color` | `CardPart.name` and `CardPart.colorIndicator []` on `createTokens` |
| `Selector.putFromBattlefieldThisTurn` | `Selector.wasObjectSince` of `Trigger.putToGraveyard` of permanents, since `Trigger.turnStart` |
| `SetPredicate.distinctNames` | No remaining card needs it; earlier tags matched “from among them” |
| `Trigger.beginStep` | `Trigger.upkeep`, `endStep`, `combatStart`, `precombatMainPhase` |
| `Trigger.becomeTarget` | `Trigger.target`, or `castSpell` of a spell that `hasTarget` |
| `Trigger.tokenEnters` | `Trigger.enter` of a selector with `Selector.token` |
| `Trigger.dealtDamage` | `Trigger.damage .all` of the damaged object |
| `Trigger.sagaChapter`, `TraditionalCardDefinition.sagaChapters`, `CounterKind.lore` | `Ability.keywordWithEffect (.chapter n)` (Armor Wars) |
| `Condition.enteredThisTurn`, `sourceEnteredThisTurn` | `Condition.happened (Trigger.enter …) .turnStart` |
| `Condition.firstThisTurn` | `Condition.didNotHappen … .turnStart` or `Trigger.ordinal` |
| `Condition.not`, `enduringStory`, `any` | The `Condition` constructors of those names |
| `Condition.controlCount`, `greaterOrEqual` of `Value.count` | `Condition.greaterOrEqual (Value.count …)` |
| `Condition.or` | `Condition.not (.and (.not a) (.not b))` |
| `Ability.activatedOnce` (power-up) | `Ability.abilityId` with `activatedWithStaticIf (didNotHappen (abilityWithIdActivated n) gameStart)` and a static `if (happened (enter this) turnStart) [reduceCost .this …]` |
| `TraditionalCardDefinition.entersTappedUnless` | `static (if (not c) [replace (enter this) [putOntoBattlefieldInState this [tapped]]])` (The Lonely Mountain) |
| `Ability.keywordWard`, `Cost.wardNonmana` | `Ability.keywordWithCost .ward` with `Cost.mana`, `discard`, `sacrificeCount`, or `or` (poison stays a gap) |
| `Ability.keywordCrew`, `Cost.tapPowerTotal` on Vehicles | `Keyword.crew n` |
| `Ability.keywordFlashback` | `Keyword.flashback` |
| `Ability.keywordTeamwork` | `Keyword.teamwork n` |
| `Ability.keywordImprovise` | `Keyword.improvise` |
| `Ability.keywordKicker` | `Keyword.kicker` with `Ability.keywordWithCost` |
| `Ability.keywordAffinity` | `Keyword.affinity` of card types and subtypes |
| `Ability.keywordBoast` | `Keyword.boast` |
| `Ability.keywordCascade` | `Keyword.cascade` (one ability per instance) |
| `Ability.keywordExtort` | `Keyword.extort` |
| `Ability.keywordSneak` | `Keyword.sneak` with `Ability.keywordWithCost` |
| `Ability.gift` | `Keyword.gift` of each gift in CR 702.174d–i. “If the gift was promised” is `Condition.giftPromised` (Bilbo's Gambit) |
| `Ability.activateFromZone` | `Ability.graveyardActivatedIf` |
| `Cost.manaX`, `Cost.life`, `Cost.or` | `ManaSymbol.x` in `Cost.mana` with `Value.x`; `Cost.life`; `Cost.or` |
| `ContinuousEffect.setPowerToughness` | `setBasePower` / `setBaseToughness` of a `Value` |
| `ContinuousEffect.addPower` / `addToughness`, `reduceCostByValue`, `reduceCostPer` | `addPower`, `addToughness`, `setPower` of a `Value`; `reduceCostWithX` |
| `ContinuousEffect.restrictManaSpend` | `actionId n` on the mana action plus `forbid (spendManaCreatedByAction n (.not …))` (Desolation of Smaug) |
| `ContinuousEffect.cantBeCountered`, `forbidCast`, `cantBeBlockedBy`, can't attack/block | `forbid` of `Trigger.counter`, `castSpell`, `block`, `attack` |
| `ContinuousEffect.skipsUntap` | `ContinuousEffect.doesntUntap` |
| `ContinuousEffect.gainAbilityIf` (flash) | `canBeCastAsThoughWithFlashIf`, with `reduceCost` under `if` |
| `ContinuousEffect.preventDamage` | `replace (Trigger.damage …) []` |
| `ContinuousEffect.replace`, `canPlay`, `gainAbility` | The constructors of those names |
| `CardAction.lookAt`, `randomize` (bottom of library), `connive`, `addManaCombination` | `lookAt`, `putOnLibraryBottomInRandomOrder`, `keyword … (.connive n)`, `addManaInAnyCombination` |
| `CardAction.chooseModes` (“choose one or both”) | `chooseUniqueModes (.range 1 2)` |
| `CardAction.chooseCreatureType`, `Selector.chosenType` | `actionId n (chooseCreatureType …)` and `Selector.hasCreatureTypeChosenByAction n` |
| `TraditionalCardDefinition.asEntersChoice` | `static (replace (enter this) [actionId n (chooseCreatureType (controller this)), keepReplacedAction])` (An Unexpected Party) |
| `CardAction.eventAmount` for “for each permanent destroyed this way” | `Value.count (Selector.wasObjectOfAction n)` |
| `CardAction.putCounter` of a `Value` | `putCounter` takes a `Value` (`x`, `count`, `greatestPower`, `greatestManaValue`) |
| `CardAction.removeCounter` | `removeCounter` of a selector, `CounterKind`, and `Value` |
| `CounterKind.named` | `burden`, `deathtouch`, `doubleStrike`, `finality`, `firstStrike`, `flying`, `haste`, `hone`, `hope`, `indestructible`, `influence`, `invasion`, `lifelink`, `menace`, `plan`, `quest`, `reach`, `shadow`, `shield`, `stun`, `trample`, `vigilance` |
| `TraditionalCardDefinition.entersWithCounters` | `static (replace (enter this) [putCounter …, keepReplacedAction])` (Dawn of a New Age, The Ruinous Wrecking Crew) |
| `Selector.manaValue` at most | `Selector.manaValueAtMost` (at least, and a total mana value, stay gaps) |

## Missing constructors by type

Each subsection lists constructors that at least one remaining supported card
needs. Card names are examples; the [per-card index](#per-card-index) is
complete.

### `SetPredicate`

- **`shareName`** (1 card) — The selected objects share a name
  - Key to the Side-Door

### `Value`

- **`counterCount`** (5 cards) — The number of counters of a kind on an object
  - Alien Invasion; Palantír of Orthanc; Red Hulk; The One Ring; Tom Bombadil
- **`greatestCountAmongPlayers`** (1 card) — The greatest count over players (greatest number of artifacts an opponent controls)
  - Cavern-Hoard Dragon
- **`lifeGainedThisTurn`** (1 card) — How much life a player gained this turn
  - The Gaffer
- **`manaSpent`** (1 card) — The amount of mana spent to cast a spell
  - Uncover the Moon-Letters
- **`manaSymbols`** (1 card) — The number of mana symbols of a color in a mana cost
  - Namor the Sub-Mariner

### `Selector`

- **`manaValue`** (19 cards) — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it
  - Bilbo, Unexpected Adventurer; Call Forth the Tempest; Cosmic Cube; Cruel Alliance; Evil's Thrall; Gandalf, Party Guest; Glamdring; Gollum, Riddle Master; Inside Information; Loki Laufeyson; … (10 more)
- **`attackingAlone`** (8 cards) — A creature attacking alone
  - Agent 13, Sharon Carter; Agents of S.H.I.E.L.D.; Bilbo's Ring; Black Widow, Double Agent; Crowd of True Believers; HYDRA Infiltration; Luke Cage, Power Man; S.H.I.E.L.D. Spy Kit
- **`attached`** (5 cards) — Objects attached to a given object (inverse of `hostOf`)
  - Long-Lost Lances; Ronin, Shadow Stalker; Thorin, Mountain-king; Whiplash, Vengeful Engineer; Winter Soldier, Icy Assassin
- **`color`** (5 cards) — Objects of a color (spells and permanents). Token colors are `CardPart.colorIndicator`
  - Aragorn, the Uniter; Baron Helmut Zemo; Goblin Cratermaker; Necklace of Girion; World War Hulk
- **`toughness`** (4 cards) — Toughness comparisons (`Value.greatestToughness` exists; `powerAtLeast` / `powerAtMost` have no toughness counterpart)
  - Baxter Building; Murdock's Crusade; Stern Scolding; The Kingpin of Crime
- **`defendingPlayer`** (3 cards) — The defending player relative to an attacker
  - Captain America's Shield; Colossal Whale; Witch-king, Bringer of Ruin
- **`powerUpAbility`** (3 cards) — Power-up abilities as a class (cost reductions, extra activations, “can't be activated”). Power-up is not a `Keyword`, so `keywordAbility` can't pick it
  - Hulk, Gamma Goliath; Kang the Conqueror; Wonder Man, Hollywood Hero
- **`damagedThisTurn`** (2 cards) — Objects that were dealt damage / dealt damage this turn
  - Bitter Downfall; Red Guardian, Super-Soldier
- **`graveyardSizeAtLeast`** (2 cards) — Graveyards (or their owners) with at least N cards, so they can be counted
  - Master's Councillors; The Master of Lake-town
- **`castFromZone`** (1 card) — Zone a spell is cast from (only `Trigger.castSpellFromGraveyard` exists)
  - Bilbo, Thief in the Night
- **`commander`** (1 card) — The selected player's commander
  - Arcane Signet
- **`mostLife`** (1 card) — A player with the most life or tied for most life
  - The Black Gate
- **`receivedCounterThisTurn`** (1 card) — Objects *you* put +1/+1 counters on this turn (`putCountersSimultaneously` does not say who put them)
  - Kid Loki
- **`sacrificedForCost`** (1 card) — The object sacrificed to pay a cost (`wasObjectOfAction` names actions, not costs)
  - Tom, Bert, and William
- **`worthy`** (1 card) — Worthy (Marvel)
  - Mjölnir, Hammer of Thor

### `Trigger`

- **`whenYouDo`** (14 cards) — Reflexive trigger after an action (“When you do, …”, CR 603.12)
  - Ant-Man, Colony Commander; Bolg of the North; Claim the Kingdom; Construct a Cosmic Cube; Death to Our Enemies; Doom Reigns Supreme; Dáin Ironfoot; Grim Reaper, Lethal Legionnaire; Hawkeye, Master Marksman; Head of the Hunt; … (4 more)
- **`leaveBattlefield`** (11 cards) — When the selected object leaves the battlefield, also as a duration bound (“until this leaves the battlefield”, “for as long as this remains on the battlefield”)
  - Banishing Light; Celebrate the Mountain-king; Cloak and Dagger, Entwined; Colossal Whale; Fiend Hunter; Old Fat Spider Can't See Me; Secret Invasion; Super Villain Lockup; The Super Hero Civil War; The Wondrous Wasp; … (1 more)
- **`onceEachTurn`** (11 cards) — “This ability triggers only once each turn” / “Do this only once each turn”. `Trigger.ordinal 1 … .turnStart` is the first event, which differs when the source arrives mid-turn. Activated “only once each turn” is `didNotHappen (abilityWithIdActivated n) turnStart`
  - Ant-Man, Colony Commander; Baron Strucker, HYDRA Overlord; Crossbones, Malicious Mercenary; Elrond, Moon-Reader; Knight of Wundagore; Loki, God of Mischief; Moon Girl and Devil Dinosaur; Nimrodel Watcher; Part in Friendship; The Sensational She-Hulk; … (1 more)
- **`attackAlone`** (8 cards) — When the selected object attacks alone
  - Agent 13, Sharon Carter; Agents of S.H.I.E.L.D.; Bilbo's Ring; Black Widow, Double Agent; Crowd of True Believers; HYDRA Infiltration; Luke Cage, Power Man; S.H.I.E.L.D. Spy Kit
- **`nextTurnOf`** (7 cards) — Duration bound “until your next turn” / “until the end of your next turn” (`endOfPlayerTurn` ends at the current turn's end)
  - Absorbing Man; Evil's Thrall; Hex Magic; Taskmaster, Mercenary Mimic; The Great Goblin; The One Ring; Thor, God of Thunder
- **`nthCounter`** (7 cards) — When the Nth counter of a kind is put on the selected object (`Trigger.ordinal` counts events, not counters)
  - Claim the Kingdom; Construct a Cosmic Cube; Death to Our Enemies; Doom Reigns Supreme; Political Triumph; Rewrite History; Robot Domination
- **`becomeTapped`** (4 cards) — When the selected object becomes tapped (including tapped to pay a cost)
  - Agent Maria Hill; Captain America, Living Legend; Hawkeye's Bow; Hawkeye, Master Marksman
- **`gainLife`** (2 cards) — Whenever the selected player gains life
  - Heroic Feast; Tigra, Feline Fury
- **`putCounter`** (2 cards) — Whenever counters of any kind are put on matching objects (`putCountersSimultaneously` takes one `CounterKind`)
  - Doc Samson, Super Psychiatrist; The Great Goblin
- **`scry`** (2 cards) — Whenever the selected player scries
  - Celeborn the Wise; Nimrodel Watcher
- **`theRingTemptsYou`** (2 cards) — Whenever the Ring tempts you / you choose a Ring-bearer
  - Sauron, the Dark Lord; Witch-king of Angmar
- **`chapterResolves`** (1 card) — Whenever the final chapter ability of a Saga resolves
  - Tom Bombadil
- **`connive`** (1 card) — When the selected creature would connive (a keyword-action event for `replace`)
  - Leader, Super-Genius
- **`loseLife`** (1 card) — Whenever the selected player loses life
  - The Master of Lake-town
- **`opponentDrawsExceptFirst`** (1 card) — An opponent draws except the first card of their draw step (same missing draw-step window as `wouldDraw`)
  - Orcish Bowmasters
- **`wouldDraw`** (1 card) — A draw other than the first in each draw step. `replace` of `Trigger.draw` is “would draw”; there is no draw-step window
  - Bard, King of Dale

### `Cost`

- **`tapPowerTotal`** (12 cards) — Tap creatures you control with total power N or more (Teamwork). Crew is `Keyword.crew`
  - Atlantis Attacks; Cruel Alliance; Earth's Mightiest Heroes; Go Nuts!; Helicarrier Strike; HULK SMASH!; Murdock's Crusade; Repulsor Blast; Team Tactics; Too Evil to Stay Dead; … (2 more)
- **`optionalAdditional`** (2 cards) — Optional additional cost (Kicker)
  - Galadriel's Dismissal; The Eagles Are Coming!
- **`tapArtifactsForGeneric`** (2 cards) — Tap artifacts to pay generic (Improvise)
  - Arc Reactor; Ironheart, Clever Champion
- **`getPoisonCounters`** (1 card) — Get poison counters as a cost (Ward—Get five poison counters). Other nonmana ward costs are `Cost.discard` / `sacrificeCount` / `or`
  - The Serpent Society
- **`tapOther`** (1 card) — Tap another matching permanent (not the tap symbol on the source)
  - The Shire

### `Condition`

- **`castWithTeamwork`** (12 cards) — This spell was cast using teamwork
  - Atlantis Attacks; Cruel Alliance; Earth's Mightiest Heroes; Go Nuts!; Helicarrier Strike; HULK SMASH!; Murdock's Crusade; Repulsor Blast; Team Tactics; Too Evil to Stay Dead; … (2 more)
- **`kicked`** (2 cards) — This spell was kicked
  - Galadriel's Dismissal; The Eagles Are Coming!
- **`manaValueParity`** (2 cards) — Mana value is odd/even
  - Gollum, Riddle Master; Thanos, the Mad Titan
- **`attackedThisTurn`** (1 card) — You attacked with N or more creatures this turn (over every combat, not one `attackSimultaneously`)
  - Minas Tirith
- **`citysBlessing`** (1 card) — You have the city's blessing
  - Andúril, Narsil Reforged
- **`resolvedThisTurnCount`** (1 card) — This ability has resolved N times this turn
  - Belladonna Took

### `Ability`

- **`linkedExile`** (8 cards) — Paired exile-until-leaves (enter trigger + leave trigger sharing exiled objects), or cards “exiled with this” across abilities
  - Banishing Light; Celebrate the Mountain-king; Cloak and Dagger, Entwined; Colossal Whale; Fiend Hunter; Roads Go Ever, Ever On; Super Villain Lockup; Web Up
- **`graveyardTriggered`** (1 card) — A triggered ability that functions while the card is in a graveyard (`graveyardActivatedIf` is activated only)
  - Silvan Reveler
- **`harness`** (1 card) — Harness and the ∞ ability that works once harnessed
  - The Mind Stone

### `ContinuousEffect`

- **`loseAbilities`** (5 cards) — Selected object loses all abilities, or a named ability
  - Enchanted River's Grasp; Frozen in Ice; Hellcat, Undying Vigilante; Smite the Deathless; The Wondrous Wasp
- **`setTypes`** (5 cards) — Set card types/subtypes rather than only gain them (“becomes an artifact creature”, “is an artifact”, copy exceptions)
  - I Am Iron Man; Iron Man Armor; Reptil, Dinomorpher; Taskmaster, Mercenary Mimic; Tom, Bert, and William
- **`mayLookAtTop`** (4 cards) — May look at the top card of the selected library any time
  - Daredevil, Man Without Fear; Elven Chorus; Iron Lad, Diverging Destiny; Ka-Zar of the Savage Land
- **`attacksEachCombat`** (3 cards) — Attacks each combat if able (“can't attack” is `forbid` of `Trigger.attack`)
  - Alien Invasion; Ares, God of War; The Sentry, Golden Guardian
- **`extraTrigger`** (3 cards) — Matching triggered abilities trigger an additional time
  - Bifur, Melodic Rider; Chief of the Wilds; Wizard's Staff
- **`handSize`** (2 cards) — Set / remove maximum hand size
  - Ms. Marvel, Kamala Khan; The Ten Rings
- **`modifyDamage`** (2 cards) — Replacement that changes how much damage is dealt
  - Hawkeye, Young Avenger; Mjölnir, Hammer of Thor
- **`replaceTokenCreation`** (2 cards) — If tokens would be created, create more or different tokens (no token-creation event for `replace`)
  - Bard, King of Dale; Bilbo, Fellow Conspirator
- **`spendManaAsThoughAnyType`** (2 cards) — Mana of any type can be spent to cast the selected spells
  - Black Widow, Super Spy; Shadow of the Enemy
- **`activateAsThoughHaste`** (1 card) — Activate abilities of the selected creatures as though they had haste
  - Shang-Chi, Master of Kung Fu
- **`cantBeBlockedByMoreThan`** (1 card) — Can't be blocked by more than N creatures
  - White Tiger, Ava Ayala
- **`cantBeBlockedExceptBy`** (1 card) — Can't be blocked except by N or more creatures (menace is Keyword for N=2)
  - Troll of Khazad-dûm
- **`cantBecomeUntapped`** (1 card) — Can't become untapped (stronger than `doesntUntap`)
  - Frozen in Ice
- **`cantBeCountered`** (1 card) — The spell a mana ability's mana was spent on can't be countered. `forbid (Trigger.counter …)` covers “this spell can't be countered”
  - Delighted Halfling
- **`copyActivatedAbilities`** (1 card) — Gains the activated abilities of matching objects
  - Thranduil, the Elvenking
- **`forbidUntapWhileYouControl`** (1 card) — Can't become untapped for as long as you control this
  - Spider-Woman, Secret Agent
- **`gainSupertype`** (1 card) — Gain a supertype in addition to other types (legendary)
  - Super-Soldier Serum
- **`reduceCost`** (1 card) — `reduceCost` + `if` exists; missing the damaged-this-turn target shape
  - Bitter Downfall
- **`reduceCostIfCastFrom`** (1 card) — Spells you cast from matching zones cost less
  - Bilbo, Thief in the Night
- **`replaceEnterCounters`** (1 card) — As matching other objects enter, they enter with extra counters
  - Arwen, Weaver of Hope
- **`setSubtypes`** (1 card) — Overwrite subtypes (`gainSubtype` only adds)
  - Fog on the Barrow-Downs

### `CardAction`

- **`copy`** (10 cards) — Copy a permanent, spell, or ability, or create token copies (`copyWithNewTargets` copies a spell with new targets only)
  - Absorbing Man; Echo, Perceptive Prodigy; Multiversal Incursion; Photon Blast Barrage; Scientist Supreme of A.I.M.; Secret Invasion; Shuri, Wakandan Inventor; Taskmaster, Mercenary Mimic; The Notary Hobbits; Ultron, Artificial Malevolence
- **`eventAmount`** (8 cards) — Use the amount from the triggering event or a previous action (“that much”, “that many”, excess damage). `defineValueVariable` records a value computed on resolution, not an event's amount
  - Bolg of the North; Doc Samson, Super Psychiatrist; Hawkeye, Young Avenger; Heroic Feast; Smaug the Impenetrable; The Master of Lake-town; The Reaver Cleaver; The Sensational She-Hulk
- **`returnExiled`** (8 cards) — Return objects exiled by a linked action
  - Banishing Light; Celebrate the Mountain-king; Cloak and Dagger, Entwined; Colossal Whale; Fiend Hunter; Roads Go Ever, Ever On; Super Villain Lockup; Web Up
- **`chooseModes`** (6 cards) — The number of modes depends on a condition known as the spell is cast (teamwork, controlling a Wizard). `chooseUniqueModes` takes a fixed `Range`
  - Atlantis Attacks; Flame of Anor; Go Nuts!; HULK SMASH!; Murdock's Crusade; Widow's Bite
- **`transform`** (6 cards) — Transform this permanent
  - Bruce Banner; Jennifer Walters; King T'Challa; Monica Rambeau; Nick Fury, Agent of S.H.I.E.L.D.; Tony Stark
- **`exileThenReturn`** (4 cards) — Exile, then return at a later event (a delayed trigger such as the next end step)
  - Elrond, Moon-Reader; Roll-Roll-Roll-Roll; S.H.I.E.L.D. Flying Car; Wiccan, Rising Magician
- **`gainControl`** (4 cards) — Gain control of selected objects
  - Bilbo's Burglaring; Evil's Thrall; Sauron, the Lidless Eye; The Super Hero Civil War
- **`addManaOfColorAmong`** (2 cards) — Add one mana of any color among selected objects or a commander's color identity
  - Arcane Signet; Mox Amber
- **`chooseOddEven`** (2 cards) — Choose odd or even
  - Gollum, Riddle Master; Thanos, the Mad Titan
- **`discardChosen`** (2 cards) — Discard a card another player chose (`discard` makes a player discard that many cards of their choice)
  - Down, Down to Goblin-town; Klaw, Sonic Subjugator
- **`exileUntil`** (2 cards) — Exile from the top of a library until a matching card
  - Black Widow, Super Spy; Gríma, Saruman's Footman
- **`extraCombat`** (2 cards) — An additional combat phase; typically with untap attackers
  - Desert Were-Worm; The Incredible Hulk
- **`investigate`** (2 cards) — Investigate / create a Clue
  - Agent 13, Sharon Carter; Panther Pounce
- **`theRingTemptsYou`** (2 cards) — The Ring tempts you
  - Sauron, the Dark Lord; Witch-king of Angmar
- **`becomeWithAbility`** (1 card) — Lose other types, become Food artifacts, and gain a stated activated ability
  - Supper for Spiders
- **`behold`** (1 card) — Behold a subtype
  - Elven Passage
- **`cascade`** (1 card) — Exile until a cheaper nonland; you may cast it
  - Call Forth the Tempest
- **`changeTargets`** (1 card) — Choose new targets for another spell or ability
  - Speedball, New Warrior
- **`extraTurn`** (1 card) — Take an extra turn
  - Kang the Conqueror
- **`forEachCounterKind`** (1 card) — For each kind of counter on a selected object, give another of that kind
  - Powerful Broker
- **`gainProtection`** (1 card) — A player gains protection from everything
  - The One Ring
- **`phaseOut`** (1 card) — Phase out
  - Galadriel's Dismissal
- **`randomize`** (1 card) — Pick a random card among (`putOnLibraryBottomInRandomOrder` exists)
  - Getaway Barrel
- **`separatePiles`** (1 card) — Separate cards into piles for an opponent to choose
  - Riddles in the Dark

### `TraditionalCardDefinition`

- **`otherFace`** (6 cards) — Second face of a transforming DFC (`CardPart.alternative` is Adventure-only)
  - Bruce Banner; Jennifer Walters; King T'Challa; Monica Rambeau; Nick Fury, Agent of S.H.I.E.L.D.; Tony Stark

## Cards with no constructor gap

The first pass listed 89 cards that the current constructors could spell.
All 89 are now `TraditionalCardDefinition`s that read their
Oracle text with `parseOracleParts`, with a `#guard` pinning each parsed
definition and the modeled `CardDef` fields `toCardDef` produces. The new
templates are in `OracleParse.lean`, and the leftovers and `CardFace` fields
they compile to are in `Definition.lean`. Wall, Minion, and Elder are
`CardSubtype`s. `Trigger.putCountersSimultaneously` names the player who put
the counters. `Trigger.enterSimultaneously` is one trigger for objects that
enter together.

**Hobbit (10):** Boughside Wanderers; Burn, Burn, Tree and Fern; Down in the Valley; Gleaming Splendor; Lake-town Toymaker; Orcrist, Goblin-cleaver; Radagast of Rhosgobel; Stone-Giant of High Pass; The Misty Mountains Cold; Through the Forest Gate.

**Hobbit Eternal (22):** Bag End Banquet; Bolg, Erebor's Reckoning; Dragon's Desire; Dwarven Warriors; Dáin of the Ancient Halls; Elvish Archdruid; Errand-Rider of Gondor; Flowering of the White Tree; Fíli and Kíli, Joyous; Haunt of the Dead Marshes; Last March of the Ents; Mentor of the Meek; Minas Tirith Garrison; Mirkwood Elk; Mount Doom; Olog-hai Crusher; Orcish Siegemaster; Ori, Plate Stacker; Raise the Palisade; Relic of Sauron; Rivendell; Thranduil the Strategist.

**Marvel Super Heroes (57):** Abomination, Terrifying Titan; Aerial Doombot; Avengers Assemble!; Avengers Disassembled; Avengers Tower; Avengers: Under Siege; Black Panther, Hope Enduring; Bold Biochemist; Brave Brawler; Captain America, Wings of Freedom; Captain Mar-Vell, Space-Born; Castle Doom; Colleen Wing, Street Samurai; Decoy Ploy; Doctor Doom; Epic Fight; Falcon's Wing Harness; H.E.R.B.I.E. Scout Unit; HYDRA Troopers; Hercules, Prince of Power; Hulkling, Burgeoning Bruiser; Human Torch, Johnny Storm; Hydraulic Helper; Invisible Woman, Sue Storm; Iron Fist, Living Weapon; Iron Man, Master of Machines; Mister Fantastic, Reed Richards; Misty Knight, Hero for Hire; Mole Man, Moloid Master; Ninja of the Hand; Pet Avengers; Punishing Punch; Raft Security Officer; Serpent Specialist; She-Hulk, Jade Defender; Super Intelligence; Super Strength; Super-Skrull; The Coming of Galactus; The Invincible Iron Man; The Unbeatable Squirrel Girl; The Vision; Titania, Rugged Rumbler; Training Regimen; U.S.Agent, John Walker; Ultron Drone; Unliving Legionnaire; Villainous Hideout; Viv Vision, Teen Synthezoid; Volcanic Villain; War Machine, Legacy of Iron; Worlds Within Worlds; Dark Fortress; Gathering Place; Gleaming Bastion; Hidden Lair; Training Compound.

## Earlier conversions

The first pass listed 44 remaining cards that did not match a missing-constructor
pattern. Conversion against `toCardDef` split them.

### Converted to `TraditionalCardDefinition`

These 30 cards now compile through leftovers onto the same modeled `CardDef`
(Oracle still matches). A later pass converted **21 more** that were blocked
only by missing `CardSubtype` constructors (now present): Troop of Ponies;
Landroval, Horizon Witness; Aragorn and Arwen, Wed; Thorin, King of Durin's
Folk; Galadriel, Light of Valinor; Night Nurse, Healer of Heroes; Quake,
Agent of S.H.I.E.L.D.; Justice, Vance Astrovik; Arnim Zola, Bio-Fanatic;
The Masters of Evil; Moonstone, Harsh Mistress; Roxxon Brutes; Fin Fang Foom;
Speed, Young Avenger; Guerrilla Gorilla; Undercover Skrull; Beast, Erudite
Aerialist; Bullseye, Death Dealer; Killmonger, Scourge of Wakanda; Storm,
Windrider; Wolverine, Fierce Fighter. Five Plan enchantments and The Great
Goblin stay in the catalog as `CardDef` helpers (put-counter triggers;
`CounterKind.plan` exists). Catalog files: `Hobbit.lean`, `HobbitEternal.lean`,
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

Since the previous revision of this index, 52 more listed cards became
`TraditionalCardDefinition`s. All of them read their Oracle text with
`parseOracleParts`.

**Hobbit (42):** An Unexpected Party; Azog, Moria's Ruin; Balin, Loremaster; Bard's Company; Bombur, Gentle Dreamer; Chief Warg's Company; Desolation of Smaug; Dwarven Mattock; Dáin's Company; Dáin, Lord of the Iron Hills; Eagle's Rescue; Esgaroth Garrison; Fíli the Pathfinder; Gandalf, Goblins' Bane; Gandalf, Wandering Wizard; Gigantic Big Bear; Glamdring, Foe-hammer; Glóin the Mighty; Great Gilded Boat; Great Ugly-Looking Goblin; Iron Hills Blacksmith; Kíli the Resourceful; Lake-town Mariners; Mirkwood Meditator; Moment of Glory; Most Decrepit Old Bird; My Precious; Old Fat Spider; Ori, Keeper of Songs; Pinecone Strike; Plunder the Trollshaws; Settle the Wreckage; Smaug the Magnificent; Smaug, Wicked Worm; The Arkenstone; The Black Arrow; The Lonely Mountain; The Lord of the Eagles; Thorin Oakenshield; Tidings of War; Troll Negotiations; Óin the Brave.

**Hobbit Eternal (1):** Treasure Vault.

**Marvel Super Heroes (9):** A.I.M. Scientists; Dependable Quinjet; Kang, Temporal Tyrant; M.O.D.O.K.; Madame Masque; Red Room Recruit; S.H.I.E.L.D. Helicarrier; Swordsman, Sharp Scoundrel; Trickster's Stratagem.

## Cards that still cannot convert

Closer reading of the remaining 12 found constructor gaps. Evidence is the
printed ability vs the current inductives (not a missing leftover for an
expressible spelling). Three of them could later be spelled and are now
`TraditionalCardDefinition`s read with `parseOracleParts`: Ori, Plate
Stacker; Captain Mar-Vell, Space-Born; and The Vision. The other nine stay
in the catalog as `CardDef` helpers.

- **Supper for Spiders** — Put onto the battlefield all creature cards in
  opponents' graveyards that were put there *from the battlefield this turn*;
  they become Food artifacts with an activated ability.
  `Selector.wasObjectSince` of `Trigger.putToGraveyard` now selects those
  cards. There is still no `CardAction` to change types to Food, losing the
  other types, and grant an ability.
- **Long-Lost Lances** — During your turn, *creatures you control that are
  equipped* have first strike and vigilance. That needs `Selector.attached`
  (inverse of `hostOf`). Equipped-creature host bonuses already exist; this
  static is the other direction.
- **Ori, Plate Stacker** — Destroy all artifacts and enchantments opponents
  control; gain 1 life *for each permanent destroyed this way*. Now
  spellable: `actionId` on the destroy and `gainLife` of
  `Value.count (Selector.wasObjectOfAction n)`. Converted.
- **Black Widow, Super Spy** — Combat-damage exile from the top until a
  nonland, then an optional +1/+1 or cast-the-exiled-card.
  `Selector.topOfLibrary` and `Selector.inExile` exist. Exile-until and
  “mana of any type can be spent” are missing.
- **Captain Mar-Vell, Space-Born** — As long as an opponent has cast a spell
  this turn, you may cast spells as though they had flash. Now spellable:
  `ContinuousEffect.canBeCastAsThoughWithFlashIf` with `Condition.happened`
  of an opponent's `castSpell` since `turnStart`. Converted.
- **Kid Loki** — Each creature you control that you've put +1/+1 counters on
  *this turn* has hexproof. `Selector.hasCounter` and `wasObjectSince` of
  `putCountersSimultaneously` exist, but that trigger does not say who put
  the counters. (The second-card +1/+1 on self is already
  leftover-expressible as `onDrawSecondPlusOne`, but the static is not.)
- **Powerful Broker** — For each *kind of counter* on target permanent or
  player, give another counter of that kind. No constructor iterates counter
  kinds.
- **Speedball, New Warrior** — Whenever a player casts a spell that targets
  Speedball, pump and *choose new targets for that spell*. The trigger is
  `Trigger.target` (or `castSpell` of a spell that `hasTarget` Speedball);
  changing targets of another spell is not a `CardAction`.
- **Spider-Man, To the Rescue** — You may tap him. *When you do*, another
  target nonattacking creature gains indestructible. Nested “when you do”
  delayed trigger is not a `Trigger` constructor.
- **Spider-Woman, Secret Agent** — Tap target opponent creature; it can't
  become untapped for as long as you control Spider-Woman.
  `ContinuousEffect.doesntUntap` covers only the untap step, and no
  duration ends when you lose control.
- **Super-Soldier Serum** — Enchanted creature is a *legendary Soldier* in
  addition to its other types, and attach *any number* of Equipment you
  control. No `ContinuousEffect.gainSupertype`; `Range.any` now covers the
  unbounded count.
- **The Vision** — Choose one *that hasn't been chosen this turn*. Now
  spellable: `CardAction.chooseModeRestricted` with
  `Trigger.modeWithIdChosen`, triggered by `castSpell` of a noncreature
  spell you control. Converted; it compiles onto
  `Effect.castingVisionModes`.

## Adjacent inductives

These are not in the requested list but block a conversion of the listed types:

| Inductive | Used by | Missing constructors that remaining cards need |
| --- | --- | --- |
| `CardSubtype` | `CardPart.subtype`, `Selector.subtype` | None for the remaining cards. Wall, Minion, and Elder exist. Five Plan enchantments and The Great Goblin stay blocked by put-counter triggers, not missing subtypes. |
| `Keyword` | `Ability.keyword`, `CardAction.keyword` | Harness (this may instead be spelled as `Ability`/`ContinuousEffect` without a `Keyword` constructor). Gift, Teamwork, Improvise, Kicker, Affinity, Boast, Cascade, Extort, and Sneak exist, as do Ward, Crew, Flashback, Connive, Amass, Recruit, and Saga chapters. Power-up is not a keyword; its once-only activation and cost reduction are spelled with existing constructors. |
| `CounterKind` | `CardAction.putCounter`, `Selector.hasCounter`, `Trigger.putCountersSimultaneously` | Each named counter in the supported catalog has its own constructor. `Trigger.putCounter` (who put them, any kind) is still missing. Lore counters are Saga chapters. |

`CardPart` also has no `loyalty` or DFC-back face (`alternative` is the
Adventure face). The back face is listed under `TraditionalCardDefinition`.
Saga chapters are `Ability.keywordWithEffect (.chapter n)`.

## Per-card index

Every remaining supported catalog card. Constructors are `Type.ctor`.
Converted cards are omitted here.

### The Hobbit (HOB) (41 cards)

**Bard, King of Dale** (`bardKingOfDale`)

- `Trigger.wouldDraw` — A draw other than the first in each draw step. `replace` of `Trigger.draw` is “would draw”; there is no draw-step window
- `ContinuousEffect.replaceTokenCreation` — If tokens would be created, create more or different tokens (no token-creation event for `replace`)

**Belladonna Took** (`belladonnaTook`)

- `Condition.resolvedThisTurnCount` — This ability has resolved N times this turn

**Bifur, Melodic Rider** (`bifurMelodicRider`)

- `ContinuousEffect.extraTrigger` — Matching triggered abilities trigger an additional time

**Bilbo, Thief in the Night** (`bilboThiefInTheNight`)

- `Selector.castFromZone` — Zone a spell is cast from (only `Trigger.castSpellFromGraveyard` exists)
- `ContinuousEffect.reduceCostIfCastFrom` — Spells you cast from matching zones cost less

**Bolg of the North** (`bolgOfTheNorth`)

- `CardAction.eventAmount` — Use the amount from the triggering event or a previous action (“that much”, “that many”, excess damage). `defineValueVariable` records a value computed on resolution, not an event's amount
- `Trigger.whenYouDo` — Reflexive trigger after an action (“When you do, …”, CR 603.12)

**Celebrate the Mountain-king** (`celebrateTheMountainKing`)

- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield, also as a duration bound (“until this leaves the battlefield”, “for as long as this remains on the battlefield”)
- `Ability.linkedExile` — Paired exile-until-leaves (enter trigger + leave trigger sharing exiled objects), or cards “exiled with this” across abilities
- `CardAction.returnExiled` — Return objects exiled by a linked action

**Desert Were-Worm** (`desertWereWorm`)

- `CardAction.extraCombat` — An additional combat phase; typically with untap attackers

**Down, Down to Goblin-town** (`downDownToGoblinTown`)

- `CardAction.discardChosen` — Discard a card another player chose (`discard` makes a player discard that many cards of their choice)

**Dáin Ironfoot** (`dainIronfoot`)

- `Trigger.whenYouDo` — Reflexive trigger after an action (“When you do, …”, CR 603.12)

**Elrond, Moon-Reader** (`elrondMoonReader`)

- `Trigger.onceEachTurn` — “This ability triggers only once each turn” / “Do this only once each turn”. `Trigger.ordinal 1 … .turnStart` is the first event, which differs when the source arrives mid-turn. Activated “only once each turn” is `didNotHappen (abilityWithIdActivated n) turnStart`
- `CardAction.exileThenReturn` — Exile, then return at a later event (a delayed trigger such as the next end step)

**Elven Passage** (`elvenPassage`)

- `CardAction.behold` — Behold a subtype

**Getaway Barrel** (`getawayBarrel`)

- `CardAction.randomize` — Pick a random card among (`putOnLibraryBottomInRandomOrder` exists)

**Gollum, Riddle Master** (`gollumRiddleMaster`)

- `CardAction.chooseOddEven` — Choose odd or even
- `Condition.manaValueParity` — Mana value is odd/even
- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it

**Head of the Hunt** (`headOfTheHunt`)

- `Trigger.whenYouDo` — Reflexive trigger after an action (“When you do, …”, CR 603.12)

**Inside Information** (`insideInformation`)

- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it

**Key to the Side-Door** (`keyToTheSideDoor`)

- `SetPredicate.shareName` — The selected objects share a name

**Master's Councillors** (`masterSCouncillors`)

- `Selector.graveyardSizeAtLeast` — Graveyards (or their owners) with at least N cards, so they can be counted

**Old Fat Spider Can't See Me** (`oldFatSpiderCanTSeeMe`)

- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield, also as a duration bound (“until this leaves the battlefield”, “for as long as this remains on the battlefield”)

**Part in Friendship** (`partInFriendship`)

- `Trigger.onceEachTurn` — “This ability triggers only once each turn” / “Do this only once each turn”. `Trigger.ordinal 1 … .turnStart` is the first event, which differs when the source arrives mid-turn. Activated “only once each turn” is `didNotHappen (abilityWithIdActivated n) turnStart`

**Riddles in the Dark** (`riddlesInTheDark`)

- `CardAction.separatePiles` — Separate cards into piles for an opponent to choose

**Roads Go Ever, Ever On** (`roadsGoEverEverOn`)

- `Ability.linkedExile` — Paired exile-until-leaves (enter trigger + leave trigger sharing exiled objects), or cards “exiled with this” across abilities
- `CardAction.returnExiled` — Return objects exiled by a linked action

**Roll-Roll-Roll-Roll** (`rollRollRollRoll`)

- `CardAction.exileThenReturn` — Exile, then return at a later event (a delayed trigger such as the next end step)

**Silvan Reveler** (`silvanReveler`)

- `Ability.graveyardTriggered` — A triggered ability that functions while the card is in a graveyard (`graveyardActivatedIf` is activated only)

**Supper for Spiders** (`supperForSpiders`)

- `CardAction.becomeWithAbility` — Lose other types, become Food artifacts, and gain a stated activated ability

**The Eagles Are Coming!** (`theEaglesAreComing`)

- `Cost.optionalAdditional` — Optional additional cost (Kicker)
- `Condition.kicked` — This spell was kicked

**The Great Goblin** (`theGreatGoblin`)

- `Trigger.putCounter` — Whenever counters of any kind are put on matching objects (`putCountersSimultaneously` takes one `CounterKind`)
- `Trigger.nextTurnOf` — Duration bound “until your next turn” / “until the end of your next turn” (`endOfPlayerTurn` ends at the current turn's end)

**The Master of Lake-town** (`theMasterOfLakeTown`)

- `CardAction.eventAmount` — Use the amount from the triggering event or a previous action (“that much”, “that many”, excess damage). `defineValueVariable` records a value computed on resolution, not an event's amount
- `Trigger.loseLife` — Whenever the selected player loses life
- `Selector.graveyardSizeAtLeast` — Graveyards (or their owners) with at least N cards, so they can be counted

**The Mountain-king's Return** (`theMountainKingSReturn`)

- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it

**The Notary Hobbits** (`theNotaryHobbits`)

- `CardAction.copy` — Copy a permanent, spell, or ability, or create token copies (`copyWithNewTargets` copies a spell with new targets only)

**Thorin, Mountain-king** (`thorinMountainKing`)

- `Selector.attached` — Objects attached to a given object (inverse of `hostOf`)

**Thranduil, the Elvenking** (`thranduilTheElvenking`)

- `ContinuousEffect.copyActivatedAbilities` — Gains the activated abilities of matching objects

**Tom, Bert, and William** (`tomBertAndWilliam`)

- `Selector.sacrificedForCost` — The object sacrificed to pay a cost (`wasObjectOfAction` names actions, not costs)
- `ContinuousEffect.setTypes` — Set card types/subtypes rather than only gain them (“becomes an artifact creature”, “is an artifact”, copy exceptions)

**Uncover the Moon-Letters** (`uncoverTheMoonLetters`)

- `Value.manaSpent` — The amount of mana spent to cast a spell

**Wizard's Staff** (`wizardSStaff`)

- `ContinuousEffect.extraTrigger` — Matching triggered abilities trigger an additional time

**Enchanted River's Grasp** (`enchantedRiverSGrasp`)

- `ContinuousEffect.loseAbilities` — Selected object loses all abilities, or a named ability

### The Hobbit Eternal (HOC) (51 cards)

**Andúril, Narsil Reforged** (`andurilNarsilReforged`)

- `Condition.citysBlessing` — You have the city's blessing

**Aragorn, the Uniter** (`aragornTheUniter`)

- `Selector.color` — Objects of a color (spells and permanents). Token colors are `CardPart.colorIndicator`

**Arcane Signet** (`arcaneSignet`)

- `Selector.commander` — The selected player's commander
- `CardAction.addManaOfColorAmong` — Add one mana of any color among selected objects or a commander's color identity

**Arwen, Weaver of Hope** (`arwenWeaverOfHope`)

- `ContinuousEffect.replaceEnterCounters` — As matching other objects enter, they enter with extra counters

**Banishing Light** (`banishingLight`)

- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield, also as a duration bound (“until this leaves the battlefield”, “for as long as this remains on the battlefield”)
- `Ability.linkedExile` — Paired exile-until-leaves (enter trigger + leave trigger sharing exiled objects), or cards “exiled with this” across abilities
- `CardAction.returnExiled` — Return objects exiled by a linked action

**Bilbo's Burglaring** (`bilboSBurglaring`)

- `CardAction.gainControl` — Gain control of selected objects

**Bilbo's Ring** (`bilboSRing`)

- `Selector.attackingAlone` — A creature attacking alone
- `Trigger.attackAlone` — When the selected object attacks alone

**Bilbo, Fellow Conspirator** (`bilboFellowConspirator`)

- `ContinuousEffect.replaceTokenCreation` — If tokens would be created, create more or different tokens (no token-creation event for `replace`)

**Bilbo, Unexpected Adventurer** (`bilboUnexpectedAdventurer`)

- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it

**Bitter Downfall** (`bitterDownfall`)

- `Selector.damagedThisTurn` — Objects that were dealt damage / dealt damage this turn
- `ContinuousEffect.reduceCost` — `reduceCost` + `if` exists; missing the damaged-this-turn target shape

**Call Forth the Tempest** (`callForthTheTempest`)

- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it
- `CardAction.cascade` — Exile until a cheaper nonland; you may cast it

**Cavern-Hoard Dragon** (`cavernHoardDragon`)

- `Value.greatestCountAmongPlayers` — The greatest count over players (greatest number of artifacts an opponent controls)

**Celeborn the Wise** (`celebornTheWise`)

- `Trigger.scry` — Whenever the selected player scries

**Chief of the Wilds** (`chiefOfTheWilds`)

- `ContinuousEffect.extraTrigger` — Matching triggered abilities trigger an additional time

**Colossal Whale** (`colossalWhale`)

- `Selector.defendingPlayer` — The defending player relative to an attacker
- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield, also as a duration bound (“until this leaves the battlefield”, “for as long as this remains on the battlefield”)
- `Ability.linkedExile` — Paired exile-until-leaves (enter trigger + leave trigger sharing exiled objects), or cards “exiled with this” across abilities
- `CardAction.returnExiled` — Return objects exiled by a linked action

**Delighted Halfling** (`delightedHalfling`)

- `ContinuousEffect.cantBeCountered` — The spell a mana ability's mana was spent on can't be countered. `forbid (Trigger.counter …)` covers “this spell can't be countered”

**Elven Chorus** (`elvenChorus`)

- `ContinuousEffect.mayLookAtTop` — May look at the top card of the selected library any time

**Fiend Hunter** (`fiendHunter`)

- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield, also as a duration bound (“until this leaves the battlefield”, “for as long as this remains on the battlefield”)
- `Ability.linkedExile` — Paired exile-until-leaves (enter trigger + leave trigger sharing exiled objects), or cards “exiled with this” across abilities
- `CardAction.returnExiled` — Return objects exiled by a linked action

**Flame of Anor** (`flameOfAnor`)

- `CardAction.chooseModes` — The number of modes depends on a condition known as the spell is cast (teamwork, controlling a Wizard). `chooseUniqueModes` takes a fixed `Range`

**Galadriel's Dismissal** (`galadrielSDismissal`)

- `Cost.optionalAdditional` — Optional additional cost (Kicker)
- `Condition.kicked` — This spell was kicked
- `CardAction.phaseOut` — Phase out

**Gandalf, Party Guest** (`gandalfPartyGuest`)

- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it

**Glamdring** (`glamdring`)

- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it

**Goblin Cratermaker** (`goblinCratermaker`)

- `Selector.color` — Objects of a color (spells and permanents). Token colors are `CardPart.colorIndicator`

**Gríma, Saruman's Footman** (`grimaSarumanSFootman`)

- `CardAction.exileUntil` — Exile from the top of a library until a matching card

**Long-Lost Lances** (`longLostLances`)

- `Selector.attached` — Objects attached to a given object (inverse of `hostOf`)

**Minas Tirith** (`minasTirith`)

- `Condition.attackedThisTurn` — You attacked with N or more creatures this turn (over every combat, not one `attackSimultaneously`)

**Mox Amber** (`moxAmber`)

- `CardAction.addManaOfColorAmong` — Add one mana of any color among selected objects or a commander's color identity

**Necklace of Girion** (`necklaceOfGirion`)

- `Selector.color` — Objects of a color (spells and permanents). Token colors are `CardPart.colorIndicator`

**Nimrodel Watcher** (`nimrodelWatcher`)

- `Trigger.scry` — Whenever the selected player scries
- `Trigger.onceEachTurn` — “This ability triggers only once each turn” / “Do this only once each turn”. `Trigger.ordinal 1 … .turnStart` is the first event, which differs when the source arrives mid-turn. Activated “only once each turn” is `didNotHappen (abilityWithIdActivated n) turnStart`

**Orcish Bowmasters** (`orcishBowmasters`)

- `Trigger.opponentDrawsExceptFirst` — An opponent draws except the first card of their draw step (same missing draw-step window as `wouldDraw`)

**Palantír of Orthanc** (`palantirOfOrthanc`)

- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it
- `Value.counterCount` — The number of counters of a kind on an object

**Saruman of Many Colors** (`sarumanOfManyColors`)

- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it
- `Trigger.whenYouDo` — Reflexive trigger after an action (“When you do, …”, CR 603.12)

**Sauron, the Dark Lord** (`sauronTheDarkLord`)

- `Trigger.theRingTemptsYou` — Whenever the Ring tempts you / you choose a Ring-bearer
- `CardAction.theRingTemptsYou` — The Ring tempts you

**Sauron, the Lidless Eye** (`sauronTheLidlessEye`)

- `CardAction.gainControl` — Gain control of selected objects

**Shadow of the Enemy** (`shadowOfTheEnemy`)

- `ContinuousEffect.spendManaAsThoughAnyType` — Mana of any type can be spent to cast the selected spells

**Smaug the Impenetrable** (`smaugTheImpenetrable`)

- `CardAction.eventAmount` — Use the amount from the triggering event or a previous action (“that much”, “that many”, excess damage). `defineValueVariable` records a value computed on resolution, not an event's amount

**Smite the Deathless** (`smiteTheDeathless`)

- `ContinuousEffect.loseAbilities` — Selected object loses all abilities, or a named ability

**Stern Scolding** (`sternScolding`)

- `Selector.toughness` — Toughness comparisons (`Value.greatestToughness` exists; `powerAtLeast` / `powerAtMost` have no toughness counterpart)

**The Black Gate** (`theBlackGate`)

- `Selector.mostLife` — A player with the most life or tied for most life

**The Gaffer** (`theGaffer`)

- `Value.lifeGainedThisTurn` — How much life a player gained this turn

**The One Ring** (`theOneRing`)

- `Value.counterCount` — The number of counters of a kind on an object
- `CardAction.gainProtection` — A player gains protection from everything
- `Trigger.nextTurnOf` — Duration bound “until your next turn” / “until the end of your next turn” (`endOfPlayerTurn` ends at the current turn's end)

**The Reaver Cleaver** (`theReaverCleaver`)

- `CardAction.eventAmount` — Use the amount from the triggering event or a previous action (“that much”, “that many”, excess damage). `defineValueVariable` records a value computed on resolution, not an event's amount

**The Shire** (`theShire`)

- `Cost.tapOther` — Tap another matching permanent (not the tap symbol on the source)

**Tom Bombadil** (`tomBombadil`)

- `Trigger.onceEachTurn` — “This ability triggers only once each turn” / “Do this only once each turn”. `Trigger.ordinal 1 … .turnStart` is the first event, which differs when the source arrives mid-turn. Activated “only once each turn” is `didNotHappen (abilityWithIdActivated n) turnStart`
- `Value.counterCount` — The number of counters of a kind on an object
- `Trigger.chapterResolves` — Whenever the final chapter ability of a Saga resolves

**Troll of Khazad-dûm** (`trollOfKhazadDum`)

- `ContinuousEffect.cantBeBlockedExceptBy` — Can't be blocked except by N or more creatures (menace is Keyword for N=2)

**Witch-king of Angmar** (`witchKingOfAngmar`)

- `Trigger.theRingTemptsYou` — Whenever the Ring tempts you / you choose a Ring-bearer
- `CardAction.theRingTemptsYou` — The Ring tempts you

**Witch-king, Bringer of Ruin** (`witchKingBringerOfRuin`)

- `Selector.defendingPlayer` — The defending player relative to an attacker

**Fog on the Barrow-Downs** (`fogOnTheBarrowDowns`)

- `ContinuousEffect.setSubtypes` — Overwrite subtypes (`gainSubtype` only adds)

### Marvel Super Heroes (MSH) (128 cards)

**Absorbing Man** (`absorbingMan`)

- `CardAction.copy` — Copy a permanent, spell, or ability, or create token copies (`copyWithNewTargets` copies a spell with new targets only)
- `Trigger.nextTurnOf` — Duration bound “until your next turn” / “until the end of your next turn” (`endOfPlayerTurn` ends at the current turn's end)

**Agent 13, Sharon Carter** (`agent13SharonCarter`)

- `Selector.attackingAlone` — A creature attacking alone
- `Trigger.attackAlone` — When the selected object attacks alone
- `CardAction.investigate` — Investigate / create a Clue

**Agent Maria Hill** (`agentMariaHill`)

- `Trigger.becomeTapped` — When the selected object becomes tapped (including tapped to pay a cost)

**Agents of S.H.I.E.L.D.** (`agentsOfSHIELD`)

- `Selector.attackingAlone` — A creature attacking alone
- `Trigger.attackAlone` — When the selected object attacks alone

**Alien Invasion** (`alienInvasion`)

- `ContinuousEffect.attacksEachCombat` — Attacks each combat if able (“can't attack” is `forbid` of `Trigger.attack`)
- `Value.counterCount` — The number of counters of a kind on an object

**Ant-Man, Colony Commander** (`antManColonyCommander`)

- `Trigger.onceEachTurn` — “This ability triggers only once each turn” / “Do this only once each turn”. `Trigger.ordinal 1 … .turnStart` is the first event, which differs when the source arrives mid-turn. Activated “only once each turn” is `didNotHappen (abilityWithIdActivated n) turnStart`
- `Trigger.whenYouDo` — Reflexive trigger after an action (“When you do, …”, CR 603.12)

**Arc Reactor** (`arcReactor`)

- `Cost.tapArtifactsForGeneric` — Tap artifacts to pay generic (Improvise)

**Ares, God of War** (`aresGodOfWar`)

- `ContinuousEffect.attacksEachCombat` — Attacks each combat if able (“can't attack” is `forbid` of `Trigger.attack`)

**Atlantis Attacks** (`atlantisAttacks`)

- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork). Crew is `Keyword.crew`
- `Condition.castWithTeamwork` — This spell was cast using teamwork
- `CardAction.chooseModes` — The number of modes depends on a condition known as the spell is cast (teamwork, controlling a Wizard). `chooseUniqueModes` takes a fixed `Range`

**Baron Helmut Zemo** (`baronHelmutZemo`)

- `Selector.color` — Objects of a color (spells and permanents). Token colors are `CardPart.colorIndicator`

**Baron Strucker, HYDRA Overlord** (`baronStruckerHYDRAOverlord`)

- `Trigger.onceEachTurn` — “This ability triggers only once each turn” / “Do this only once each turn”. `Trigger.ordinal 1 … .turnStart` is the first event, which differs when the source arrives mid-turn. Activated “only once each turn” is `didNotHappen (abilityWithIdActivated n) turnStart`

**Baxter Building** (`baxterBuilding`)

- `Selector.toughness` — Toughness comparisons (`Value.greatestToughness` exists; `powerAtLeast` / `powerAtMost` have no toughness counterpart)

**Black Widow, Double Agent** (`blackWidowDoubleAgent`)

- `Selector.attackingAlone` — A creature attacking alone
- `Trigger.attackAlone` — When the selected object attacks alone

**Black Widow, Super Spy** (`blackWidowSuperSpy`)

- `CardAction.exileUntil` — Exile from the top of a library until a matching card
- `ContinuousEffect.spendManaAsThoughAnyType` — Mana of any type can be spent to cast the selected spells

**Bruce Banner** (`bruceBanner`)

- `TraditionalCardDefinition.otherFace` — Second face of a transforming DFC (`CardPart.alternative` is Adventure-only)
- `CardAction.transform` — Transform this permanent

**Captain America's Shield** (`captainAmericaSShield`)

- `Selector.defendingPlayer` — The defending player relative to an attacker

**Captain America, Living Legend** (`captainAmericaLivingLegend`)

- `Trigger.becomeTapped` — When the selected object becomes tapped (including tapped to pay a cost)

**Claim the Kingdom** (`claimTheKingdom`)

- `Trigger.nthCounter` — When the Nth counter of a kind is put on the selected object (`Trigger.ordinal` counts events, not counters)
- `Trigger.whenYouDo` — Reflexive trigger after an action (“When you do, …”, CR 603.12)

**Cloak and Dagger, Entwined** (`cloakAndDaggerEntwined`)

- `Ability.linkedExile` — Paired exile-until-leaves (enter trigger + leave trigger sharing exiled objects), or cards “exiled with this” across abilities
- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield, also as a duration bound (“until this leaves the battlefield”, “for as long as this remains on the battlefield”)
- `CardAction.returnExiled` — Return objects exiled by a linked action

**Construct a Cosmic Cube** (`constructACosmicCube`)

- `Trigger.nthCounter` — When the Nth counter of a kind is put on the selected object (`Trigger.ordinal` counts events, not counters)
- `Trigger.whenYouDo` — Reflexive trigger after an action (“When you do, …”, CR 603.12)

**Cosmic Cube** (`cosmicCube`)

- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it

**Crossbones, Malicious Mercenary** (`crossbonesMaliciousMercenary`)

- `Trigger.onceEachTurn` — “This ability triggers only once each turn” / “Do this only once each turn”. `Trigger.ordinal 1 … .turnStart` is the first event, which differs when the source arrives mid-turn. Activated “only once each turn” is `didNotHappen (abilityWithIdActivated n) turnStart`

**Crowd of True Believers** (`crowdOfTrueBelievers`)

- `Selector.attackingAlone` — A creature attacking alone
- `Trigger.attackAlone` — When the selected object attacks alone

**Cruel Alliance** (`cruelAlliance`)

- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it
- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork). Crew is `Keyword.crew`
- `Condition.castWithTeamwork` — This spell was cast using teamwork

**Daredevil, Man Without Fear** (`daredevilManWithoutFear`)

- `ContinuousEffect.mayLookAtTop` — May look at the top card of the selected library any time

**Death to Our Enemies** (`deathToOurEnemies`)

- `Trigger.nthCounter` — When the Nth counter of a kind is put on the selected object (`Trigger.ordinal` counts events, not counters)
- `Trigger.whenYouDo` — Reflexive trigger after an action (“When you do, …”, CR 603.12)

**Doc Samson, Super Psychiatrist** (`docSamsonSuperPsychiatrist`)

- `Trigger.putCounter` — Whenever counters of any kind are put on matching objects (`putCountersSimultaneously` takes one `CounterKind`)
- `CardAction.eventAmount` — Use the amount from the triggering event or a previous action (“that much”, “that many”, excess damage). `defineValueVariable` records a value computed on resolution, not an event's amount

**Doom Reigns Supreme** (`doomReignsSupreme`)

- `Trigger.nthCounter` — When the Nth counter of a kind is put on the selected object (`Trigger.ordinal` counts events, not counters)
- `Trigger.whenYouDo` — Reflexive trigger after an action (“When you do, …”, CR 603.12)

**Earth's Mightiest Heroes** (`earthSMightiestHeroes`)

- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork). Crew is `Keyword.crew`
- `Condition.castWithTeamwork` — This spell was cast using teamwork

**Echo, Perceptive Prodigy** (`echoPerceptiveProdigy`)

- `CardAction.copy` — Copy a permanent, spell, or ability, or create token copies (`copyWithNewTargets` copies a spell with new targets only)

**Evil's Thrall** (`evilSThrall`)

- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it
- `CardAction.gainControl` — Gain control of selected objects
- `Trigger.nextTurnOf` — Duration bound “until your next turn” / “until the end of your next turn” (`endOfPlayerTurn` ends at the current turn's end)

**Frozen in Ice** (`frozenInIce`)

- `ContinuousEffect.loseAbilities` — Selected object loses all abilities, or a named ability
- `ContinuousEffect.cantBecomeUntapped` — Can't become untapped (stronger than `doesntUntap`)

**Go Nuts!** (`goNuts`)

- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork). Crew is `Keyword.crew`
- `Condition.castWithTeamwork` — This spell was cast using teamwork
- `CardAction.chooseModes` — The number of modes depends on a condition known as the spell is cast (teamwork, controlling a Wizard). `chooseUniqueModes` takes a fixed `Range`

**Grim Reaper, Lethal Legionnaire** (`grimReaperLethalLegionnaire`)

- `Trigger.whenYouDo` — Reflexive trigger after an action (“When you do, …”, CR 603.12)

**HULK SMASH!** (`hULKSMASH`)

- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork). Crew is `Keyword.crew`
- `Condition.castWithTeamwork` — This spell was cast using teamwork
- `CardAction.chooseModes` — The number of modes depends on a condition known as the spell is cast (teamwork, controlling a Wizard). `chooseUniqueModes` takes a fixed `Range`

**HYDRA Infiltration** (`hYDRAInfiltration`)

- `Selector.attackingAlone` — A creature attacking alone
- `Trigger.attackAlone` — When the selected object attacks alone

**Hawkeye's Bow** (`hawkeyeSBow`)

- `Trigger.becomeTapped` — When the selected object becomes tapped (including tapped to pay a cost)

**Hawkeye, Master Marksman** (`hawkeyeMasterMarksman`)

- `Trigger.becomeTapped` — When the selected object becomes tapped (including tapped to pay a cost)
- `Trigger.whenYouDo` — Reflexive trigger after an action (“When you do, …”, CR 603.12)

**Hawkeye, Young Avenger** (`hawkeyeYoungAvenger`)

- `ContinuousEffect.modifyDamage` — Replacement that changes how much damage is dealt
- `CardAction.eventAmount` — Use the amount from the triggering event or a previous action (“that much”, “that many”, excess damage). `defineValueVariable` records a value computed on resolution, not an event's amount

**Helicarrier Strike** (`helicarrierStrike`)

- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork). Crew is `Keyword.crew`
- `Condition.castWithTeamwork` — This spell was cast using teamwork

**Hellcat, Undying Vigilante** (`hellcatUndyingVigilante`)

- `ContinuousEffect.loseAbilities` — Selected object loses all abilities, or a named ability

**Heroic Feast** (`heroicFeast`)

- `Trigger.gainLife` — Whenever the selected player gains life
- `CardAction.eventAmount` — Use the amount from the triggering event or a previous action (“that much”, “that many”, excess damage). `defineValueVariable` records a value computed on resolution, not an event's amount

**Hex Magic** (`hexMagic`)

- `Trigger.nextTurnOf` — Duration bound “until your next turn” / “until the end of your next turn” (`endOfPlayerTurn` ends at the current turn's end)

**Hulk, Gamma Goliath** (`hulkGammaGoliath`)

- `Selector.powerUpAbility` — Power-up abilities as a class (cost reductions, extra activations, “can't be activated”). Power-up is not a `Keyword`, so `keywordAbility` can't pick it

**I Am Iron Man** (`iAmIronMan`)

- `ContinuousEffect.setTypes` — Set card types/subtypes rather than only gain them (“becomes an artifact creature”, “is an artifact”, copy exceptions)

**Iron Lad, Diverging Destiny** (`ironLadDivergingDestiny`)

- `ContinuousEffect.mayLookAtTop` — May look at the top card of the selected library any time

**Iron Man Armor** (`ironManArmor`)

- `ContinuousEffect.setTypes` — Set card types/subtypes rather than only gain them (“becomes an artifact creature”, “is an artifact”, copy exceptions)

**Ironheart, Clever Champion** (`ironheartCleverChampion`)

- `Cost.tapArtifactsForGeneric` — Tap artifacts to pay generic (Improvise)

**Jennifer Walters** (`jenniferWalters`)

- `TraditionalCardDefinition.otherFace` — Second face of a transforming DFC (`CardPart.alternative` is Adventure-only)
- `CardAction.transform` — Transform this permanent

**Ka-Zar of the Savage Land** (`kaZarOfTheSavageLand`)

- `ContinuousEffect.mayLookAtTop` — May look at the top card of the selected library any time

**Kang the Conqueror** (`kangTheConqueror`)

- `CardAction.extraTurn` — Take an extra turn
- `Selector.powerUpAbility` — Power-up abilities as a class (cost reductions, extra activations, “can't be activated”). Power-up is not a `Keyword`, so `keywordAbility` can't pick it

**Kid Loki** (`kidLoki`)

- `Selector.receivedCounterThisTurn` — Objects *you* put +1/+1 counters on this turn (`putCountersSimultaneously` does not say who put them)

**King T'Challa** (`kingTChalla`)

- `TraditionalCardDefinition.otherFace` — Second face of a transforming DFC (`CardPart.alternative` is Adventure-only)
- `CardAction.transform` — Transform this permanent

**Klaw, Sonic Subjugator** (`klawSonicSubjugator`)

- `CardAction.discardChosen` — Discard a card another player chose (`discard` makes a player discard that many cards of their choice)

**Knight of Wundagore** (`knightOfWundagore`)

- `Trigger.onceEachTurn` — “This ability triggers only once each turn” / “Do this only once each turn”. `Trigger.ordinal 1 … .turnStart` is the first event, which differs when the source arrives mid-turn. Activated “only once each turn” is `didNotHappen (abilityWithIdActivated n) turnStart`

**Leader, Super-Genius** (`leaderSuperGenius`)

- `Trigger.connive` — When the selected creature would connive (a keyword-action event for `replace`)

**Loki Laufeyson** (`lokiLaufeyson`)

- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it

**Loki, God of Mischief** (`lokiGodOfMischief`)

- `Trigger.onceEachTurn` — “This ability triggers only once each turn” / “Do this only once each turn”. `Trigger.ordinal 1 … .turnStart` is the first event, which differs when the source arrives mid-turn. Activated “only once each turn” is `didNotHappen (abilityWithIdActivated n) turnStart`

**Luke Cage, Power Man** (`lukeCagePowerMan`)

- `Selector.attackingAlone` — A creature attacking alone
- `Trigger.attackAlone` — When the selected object attacks alone

**Mjölnir, Hammer of Thor** (`mjLnirHammerOfThor`)

- `Selector.worthy` — Worthy (Marvel)
- `ContinuousEffect.modifyDamage` — Replacement that changes how much damage is dealt

**Monica Rambeau** (`monicaRambeau`)

- `TraditionalCardDefinition.otherFace` — Second face of a transforming DFC (`CardPart.alternative` is Adventure-only)
- `CardAction.transform` — Transform this permanent

**Moon Girl and Devil Dinosaur** (`moonGirlAndDevilDinosaur`)

- `Trigger.onceEachTurn` — “This ability triggers only once each turn” / “Do this only once each turn”. `Trigger.ordinal 1 … .turnStart` is the first event, which differs when the source arrives mid-turn. Activated “only once each turn” is `didNotHappen (abilityWithIdActivated n) turnStart`

**Ms. Marvel, Kamala Khan** (`msMarvelKamalaKhan`)

- `ContinuousEffect.handSize` — Set / remove maximum hand size

**Multiversal Incursion** (`multiversalIncursion`)

- `CardAction.copy` — Copy a permanent, spell, or ability, or create token copies (`copyWithNewTargets` copies a spell with new targets only)

**Murdock's Crusade** (`murdockSCrusade`)

- `Selector.toughness` — Toughness comparisons (`Value.greatestToughness` exists; `powerAtLeast` / `powerAtMost` have no toughness counterpart)
- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it
- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork). Crew is `Keyword.crew`
- `Condition.castWithTeamwork` — This spell was cast using teamwork
- `CardAction.chooseModes` — The number of modes depends on a condition known as the spell is cast (teamwork, controlling a Wizard). `chooseUniqueModes` takes a fixed `Range`

**Namor the Sub-Mariner** (`namorTheSubMariner`)

- `Value.manaSymbols` — The number of mana symbols of a color in a mana cost

**Nick Fury, Agent of S.H.I.E.L.D.** (`nickFuryAgentOfSHIELD`)

- `TraditionalCardDefinition.otherFace` — Second face of a transforming DFC (`CardPart.alternative` is Adventure-only)
- `CardAction.transform` — Transform this permanent

**Origin of the Avengers** (`originOfTheAvengers`)

- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it

**Panther Pounce** (`pantherPounce`)

- `CardAction.investigate` — Investigate / create a Clue

**Photon Blast Barrage** (`photonBlastBarrage`)

- `CardAction.copy` — Copy a permanent, spell, or ability, or create token copies (`copyWithNewTargets` copies a spell with new targets only)

**Political Triumph** (`politicalTriumph`)

- `Trigger.nthCounter` — When the Nth counter of a kind is put on the selected object (`Trigger.ordinal` counts events, not counters)

**Powerful Broker** (`powerfulBroker`)

- `CardAction.forEachCounterKind` — For each kind of counter on a selected object, give another of that kind

**Red Guardian, Super-Soldier** (`redGuardianSuperSoldier`)

- `Selector.damagedThisTurn` — Objects that were dealt damage / dealt damage this turn

**Red Hulk** (`redHulk`)

- `Value.counterCount` — The number of counters of a kind on an object
- `Trigger.whenYouDo` — Reflexive trigger after an action (“When you do, …”, CR 603.12)

**Reptil, Dinomorpher** (`reptilDinomorpher`)

- `ContinuousEffect.setTypes` — Set card types/subtypes rather than only gain them (“becomes an artifact creature”, “is an artifact”, copy exceptions)

**Repulsor Blast** (`repulsorBlast`)

- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork). Crew is `Keyword.crew`
- `Condition.castWithTeamwork` — This spell was cast using teamwork

**Rewrite History** (`rewriteHistory`)

- `Trigger.nthCounter` — When the Nth counter of a kind is put on the selected object (`Trigger.ordinal` counts events, not counters)
- `Trigger.whenYouDo` — Reflexive trigger after an action (“When you do, …”, CR 603.12)

**Robot Domination** (`robotDomination`)

- `Trigger.nthCounter` — When the Nth counter of a kind is put on the selected object (`Trigger.ordinal` counts events, not counters)

**Ronin, Shadow Stalker** (`roninShadowStalker`)

- `Selector.attached` — Objects attached to a given object (inverse of `hostOf`)

**S.H.I.E.L.D. Flying Car** (`sHIELDFlyingCar`)

- `CardAction.exileThenReturn` — Exile, then return at a later event (a delayed trigger such as the next end step)

**S.H.I.E.L.D. Spy Kit** (`sHIELDSpyKit`)

- `Selector.attackingAlone` — A creature attacking alone
- `Trigger.attackAlone` — When the selected object attacks alone

**Scientist Supreme of A.I.M.** (`scientistSupremeOfAIM`)

- `CardAction.copy` — Copy a permanent, spell, or ability, or create token copies (`copyWithNewTargets` copies a spell with new targets only)

**Secret Invasion** (`secretInvasion`)

- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield, also as a duration bound (“until this leaves the battlefield”, “for as long as this remains on the battlefield”)
- `CardAction.copy` — Copy a permanent, spell, or ability, or create token copies (`copyWithNewTargets` copies a spell with new targets only)

**Shang-Chi, Master of Kung Fu** (`shangChiMasterOfKungFu`)

- `ContinuousEffect.activateAsThoughHaste` — Activate abilities of the selected creatures as though they had haste

**Shuri, Wakandan Inventor** (`shuriWakandanInventor`)

- `CardAction.copy` — Copy a permanent, spell, or ability, or create token copies (`copyWithNewTargets` copies a spell with new targets only)

**Speedball, New Warrior** (`speedballNewWarrior`)

- `CardAction.changeTargets` — Choose new targets for another spell or ability

**Spider-Man, To the Rescue** (`spiderManToTheRescue`)

- `Trigger.whenYouDo` — Reflexive trigger after an action (“When you do, …”, CR 603.12)

**Spider-Woman, Secret Agent** (`spiderWomanSecretAgent`)

- `ContinuousEffect.forbidUntapWhileYouControl` — Can't become untapped for as long as you control this

**Super Villain Lockup** (`superVillainLockup`)

- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield, also as a duration bound (“until this leaves the battlefield”, “for as long as this remains on the battlefield”)
- `Ability.linkedExile` — Paired exile-until-leaves (enter trigger + leave trigger sharing exiled objects), or cards “exiled with this” across abilities
- `CardAction.returnExiled` — Return objects exiled by a linked action

**Super-Soldier Serum** (`superSoldierSerum`)

- `ContinuousEffect.gainSupertype` — Gain a supertype in addition to other types (legendary)

**Taskmaster, Mercenary Mimic** (`taskmasterMercenaryMimic`)

- `CardAction.copy` — Copy a permanent, spell, or ability, or create token copies (`copyWithNewTargets` copies a spell with new targets only)
- `ContinuousEffect.setTypes` — Set card types/subtypes rather than only gain them (“becomes an artifact creature”, “is an artifact”, copy exceptions)
- `Trigger.nextTurnOf` — Duration bound “until your next turn” / “until the end of your next turn” (`endOfPlayerTurn` ends at the current turn's end)

**Team Tactics** (`teamTactics`)

- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork). Crew is `Keyword.crew`
- `Condition.castWithTeamwork` — This spell was cast using teamwork

**Thanos, the Mad Titan** (`thanosTheMadTitan`)

- `CardAction.chooseOddEven` — Choose odd or even
- `Condition.manaValueParity` — Mana value is odd/even
- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it

**The Incredible Hulk** (`theIncredibleHulk`)

- `CardAction.extraCombat` — An additional combat phase; typically with untap attackers

**The Kingpin of Crime** (`theKingpinOfCrime`)

- `Selector.toughness` — Toughness comparisons (`Value.greatestToughness` exists; `powerAtLeast` / `powerAtMost` have no toughness counterpart)

**The Mind Stone** (`theMindStone`)

- `Ability.harness` — Harness and the ∞ ability that works once harnessed

**The Scarlet Witch** (`theScarletWitch`)

- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it

**The Sensational She-Hulk** (`theSensationalSheHulk`)

- `CardAction.eventAmount` — Use the amount from the triggering event or a previous action (“that much”, “that many”, excess damage). `defineValueVariable` records a value computed on resolution, not an event's amount
- `Trigger.onceEachTurn` — “This ability triggers only once each turn” / “Do this only once each turn”. `Trigger.ordinal 1 … .turnStart` is the first event, which differs when the source arrives mid-turn. Activated “only once each turn” is `didNotHappen (abilityWithIdActivated n) turnStart`

**The Sentry, Golden Guardian** (`theSentryGoldenGuardian`)

- `ContinuousEffect.attacksEachCombat` — Attacks each combat if able (“can't attack” is `forbid` of `Trigger.attack`)

**The Serpent Society** (`theSerpentSociety`)

- `Cost.getPoisonCounters` — Get poison counters as a cost (Ward—Get five poison counters). Other nonmana ward costs are `Cost.discard` / `sacrificeCount` / `or`

**The Super Hero Civil War** (`theSuperHeroCivilWar`)

- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it
- `CardAction.gainControl` — Gain control of selected objects
- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield, also as a duration bound (“until this leaves the battlefield”, “for as long as this remains on the battlefield”)

**The Ten Rings** (`theTenRings`)

- `ContinuousEffect.handSize` — Set / remove maximum hand size

**The Wondrous Wasp** (`theWondrousWasp`)

- `ContinuousEffect.loseAbilities` — Selected object loses all abilities, or a named ability
- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield, also as a duration bound (“until this leaves the battlefield”, “for as long as this remains on the battlefield”)

**Thor, God of Thunder** (`thorGodOfThunder`)

- `Trigger.nextTurnOf` — Duration bound “until your next turn” / “until the end of your next turn” (`endOfPlayerTurn` ends at the current turn's end)

**Tigra, Feline Fury** (`tigraFelineFury`)

- `Trigger.gainLife` — Whenever the selected player gains life

**Tony Stark** (`tonyStark`)

- `TraditionalCardDefinition.otherFace` — Second face of a transforming DFC (`CardPart.alternative` is Adventure-only)
- `CardAction.transform` — Transform this permanent

**Too Evil to Stay Dead** (`tooEvilToStayDead`)

- `Selector.manaValue` — Mana value at least N, or a total mana value. At most is `Selector.manaValueAtMost`. `Value.greatestManaValue` names one mana value; nothing compares it inside a selector or sums it
- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork). Crew is `Keyword.crew`
- `Condition.castWithTeamwork` — This spell was cast using teamwork

**Ultron, Artificial Malevolence** (`ultronArtificialMalevolence`)

- `CardAction.copy` — Copy a permanent, spell, or ability, or create token copies (`copyWithNewTargets` copies a spell with new targets only)

**We Say Thee Nay!** (`weSayTheeNay`)

- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork). Crew is `Keyword.crew`
- `Condition.castWithTeamwork` — This spell was cast using teamwork

**Web Up** (`webUp`)

- `Trigger.leaveBattlefield` — When the selected object leaves the battlefield, also as a duration bound (“until this leaves the battlefield”, “for as long as this remains on the battlefield”)
- `Ability.linkedExile` — Paired exile-until-leaves (enter trigger + leave trigger sharing exiled objects), or cards “exiled with this” across abilities
- `CardAction.returnExiled` — Return objects exiled by a linked action

**Whiplash, Vengeful Engineer** (`whiplashVengefulEngineer`)

- `Selector.attached` — Objects attached to a given object (inverse of `hostOf`)

**White Tiger, Ava Ayala** (`whiteTigerAvaAyala`)

- `ContinuousEffect.cantBeBlockedByMoreThan` — Can't be blocked by more than N creatures

**Wiccan, Rising Magician** (`wiccanRisingMagician`)

- `CardAction.exileThenReturn` — Exile, then return at a later event (a delayed trigger such as the next end step)

**Widow's Bite** (`widowSBite`)

- `Cost.tapPowerTotal` — Tap creatures you control with total power N or more (Teamwork). Crew is `Keyword.crew`
- `Condition.castWithTeamwork` — This spell was cast using teamwork
- `CardAction.chooseModes` — The number of modes depends on a condition known as the spell is cast (teamwork, controlling a Wizard). `chooseUniqueModes` takes a fixed `Range`

**Winter Soldier, Icy Assassin** (`winterSoldierIcyAssassin`)

- `Selector.attached` — Objects attached to a given object (inverse of `hostOf`)

**Wonder Man, Hollywood Hero** (`wonderManHollywoodHero`)

- `Selector.powerUpAbility` — Power-up abilities as a class (cost reductions, extra activations, “can't be activated”). Power-up is not a `Keyword`, so `keywordAbility` can't pick it

**World War Hulk** (`worldWarHulk`)

- `Selector.color` — Objects of a color (spells and permanents). Token colors are `CardPart.colorIndicator`

## Tags now spelled, not yet converted

These 13 cards lost every tag and are still `CardDef` helpers. They lost
them when a constructor for each named counter, `CardAction.removeCounter`,
`CardAction.putCounter` of a `Value`, and enters-with-counters became
expressible. A later pass should reread them before conversion.

**Hobbit (3):** Beorn the Fierce; Dwalin, Weaponmaster; Last Light of Durin's Day.

**Hobbit Eternal (2):** Arwen, Mortal Queen; Minas Morgul, Dark Fortress.

**Marvel Super Heroes (8):** Captain America, Super-Soldier; Captain Marvel, Earth's Protector; Jessica Jones, Private Eye; Mister Hyde, Monster Within; Quicksilver, Brash Blur; Super-Adaptoid; The Astonishing Ant-Man; Thunderbolts Conspiracy.

## Method notes

- A card is “remaining” when its catalog `def` is a `CardDef` that is not
  compiled from a `TraditionalCardDefinition` with `toCardDef`.
- Tags come from Oracle text plus modeled fields (`triggeredAbilities`,
  `staticAbilities`, `Effect.*`, CardDef flags such as `teamwork`, `otherFace`,
  `saga`, `crew`, `ward`, …).
- Every tag was rechecked against the current constructors. Tags that the
  current types can spell were dropped (see
  [Former gaps that current constructors cover](#former-gaps-that-current-constructors-cover)),
  and cards left without a tag were reread for gaps the earlier pass missed.
- Reminder text in parentheses can still mention tokens (Amass, Recruit).
  Token-creation tags therefore include those ability words.
- `toCardDef` compilation and `parseOracleParts` gaps are out of scope except
  where the types themselves cannot name the ability.
