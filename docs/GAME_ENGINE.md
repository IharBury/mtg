# Game Rules Engine (`Mtg/Engine/Game/`)

This document describes the runtime state machine, module layering, casting/activation flows, effect/trigger resolution pipelines, and interactive `Pending` choice mechanisms in `Mtg/Engine/Game/`.

---

## 1. Module Layering & Inventory (50 Modules + `Game.lean`)

The 50 files in `Mtg/Engine/Game/` form a strict, acyclic import hierarchy from `Status.lean` at the bottom to `Start.lean` at the top, re-exported by `Mtg/Engine/Game.lean`:

### Layer 1: Core State & Representation
| Module | Key Types & Entry Points |
| --- | --- |
| `Status.lean` | `Status` (~75 per-permanent battlefield state fields: tapped, summoningSick, attacking/blocking, counter counts with uniform `Status.counter` / `Status.setCounter` over `CounterKind.all` (CR 122.1), temporary P/T & keyword grants, and the table-driven `untilEotFields : List UntilEotField` reset by `Status.clearedAtCleanup`). |
| `Object.lean` | `PlayPermission`, `GameObject` (~40 fields: `id`, `printed : CardDef`, `owner`, `controller`, `zone`, `status`, `timestamp`, `abilityEffect`, `triggeredAbility`, `reflexiveResolution`, `linkedExile`, copy/control tracking), `CreatureCombatAssignment`, `WaitingTrigger`. |
| `Stack.lean` | `Target` (`.player`, `.permanent`, `.card`), `StackEntry`, `ProposalKind` (`.spell`, `.activatedAbility`), and `ProposedSpell` (snapshot used to reverse illegal proposals per CR 733.1). |
| `Pending.lean` | `RandomRequest`, `AfterRandom`, `WardCost`/`WardObligation`, `SearchDest`, `CostPick`, `CardChoice`, `FraChoice` (4 category constructors over `HandGraveyardChoice`, `LibraryChoice`, `BattlefieldChoice`, `CostModeChoice`, with choice continuations carrying `Resolution` and sacrifice filters carrying `ObjectSelector`), and `Pending` (6 category constructors). |
| `Player.lean` | `GameResult`, `Player` (~48 fields: `library`, `hand`, `graveyard`, `manaPool`, life/poison, emblems/designations, per-turn counters), `Seat`, `StartConfig`, and `Action` (38 player action constructors). |
| `Core.lean` | `TriggerSequenceRest`, `TriggerOrRest`, `ChooseModesRest`, `Game` (~110 fields), and core object/player/zone accessors (`player`, `modifyPlayer`, `findObject?`, `setObject`, `mapObjectStatus`, `battlefield`, `permanentsOf`, `decidesFor`, `canSeeAs`, `followMoved`). |

### Layer 2: Continuous Effects, Zone Movement, P/T, Keywords & SBAs
| Module | Key Responsibilities |
| --- | --- |
| `Designations.lean` | Enduring story, The Ring / Ring-bearer (`setRingBearer`), City's Blessing (`checkAscend`), shadow counters. |
| `Phasing.lean` | Phasing out/in (`phaseOut`, `phaseIn`, `phaseInControlled`) and `removeFromCombat`. |
| `Allocation.lean` | ID/timestamp allocation (`allocId`, `bumpTime`, `allocObject`, `putStackEntry`, `putStackAbility`). |
| `Tokens.lean` | Predefined token `CardDef`s and token creation (`createToken`, `createKindTokens`, `empowerJace`) with token-doubling/replacement support. |
| `Attachments.lean` | Aura/Equipment attachment & cleanup (`attachSourceTo`, `unattachFrom`, `ceaseToExist`). |
| `PowerToughness.lean` | Layer 7a/7b CDAs and base P/T overrides (`characteristicBasePT`, CR 604.3 / 613.4a–b), Layer 7c continuous P/T bonuses (`lordStatBonus`, `attachedStatBonus`, `fraStatBonus`, `snapshotPT`, CR 613.4c), effective subtypes (`currentSubtypes`, `hasSubtype`, CR 613.1d), public P/T queries (`basePower`, `baseToughness`, `power`, `toughness`, `greatestPowerAmongCreatures`), and blocker lookups (`blockersOf`, `creaturesBlockedBy`). |
| `Movement.lean` | Zone-change engine (`Game.move`, `moveToOwnerGraveyard`, `moveSimultaneousToGraveyard`, `putOntoBattlefield`, `becomePrepared`/`unprepare`). Allocates a new `ObjectId` on every zone change (CR 400.7), records `(oldId, newId)` in `g.movedIds`, captures LKI snapshots, applies exile replacement effects, and queues dies/LTB/discard triggers. |
| `Leaving.lean` | Multiplayer win/loss & CR 800.4 cleanup (`decideGameIfFinished`, `changeControl`, `endControlChangingEffect`, `redirectPendingAfterLeave`, `playerLeavesGame`, `emptyManaPools`). |
| `Library.lean` | Drawing (`drawOneCard`, `draw`), `beginRecruit`, `shuffleLibrary`, `requestShuffle`, `moveIdsInOrder`, `putIdsOnTop`, `requestOrderInto`. |
| `Keywords.lean` | Effective keywords (`currentKeywords`, `fraGrantedKeywords`), `entersTapped`, attack/block legality (`canAttack`, `canBlock`), `hasHexproof`, `frcProtectedFrom`, `hasIndestructible`, `hasTrample`. |
| `CombatAssignment.lean` | Lethal damage calculation (`lethalRemaining`), `creaturesAssigningCombatDamage`, `needsCombatDamageChoice`. |
| `StateBasedActions.lean` | CR 704 SBA loop (`checkSBACounted`, `checkSBA`, `firstLegendRuleChoice?`). |
| `Timing.lean` | Priority & timing (`playersReceivePriority`, `asSorcery?`, `splitSecondOnStack`, `hasPriority`, `canPlayLand`, `mayPlayFromExile`/`mayPlayFromGraveyard`/`mayPlayFromLibraryTop`). |

### Layer 3: Targeting, Trigger Queueing, Enters, Mana & Casting
| Module | Key Responsibilities |
| --- | --- |
| `Targeting.lean` | Target legality (`canBeTargetedBy`, `matchesTargetFilter`, `legalFilteredTargets`, `legalTargetsForAtomicKind`, `legalTargetsForKind`, `triggerNeedingTargets`). |
| `Triggers.lean` | Trigger queueing & APNAP stacking (`queueTrigger`, `putTriggeredAbilityOnStack`, `putControlledTriggers`, `putFraEventTriggers`, `fraConditionHolds`, `triggerConditionHolds`, `receivePriority`, `addLoreCounters`, `becomeTapped`, `afterLifeLost`, `beginScry`). |
| `Entering.lean` | Cast triggers (`putCastTriggersOnStack`), ETB replacement (`applyEntersWith`), and ETB triggers (`afterPermanentEnters`, `afterLandEnters`, `flushTokenEnters`). |
| `ActivationCosts.lean` | Non-mana activation costs (`payLifeCost`, `costPickCandidates`, `payCostPick`, `payActivationExtraCosts`). |
| `ManaAbilities.lean` | Mana ability synthesis and execution (`ManaAbilityDef`, `manaAbilityDefs`, `activateManaAbility`, `tapForMana`). |
| `LandsAndMana.lean` | `playLand`, `manaSources`, `availableManaExcept`. |
| `SpellTargets.lean` | Proposal mode/target bounds (`spellEffectOf`, `legalModes`, `targetingOf`, `legalProposedTargets`, `announcedTargetBounds`, `defaultTarget`). |
| `Casting.lean` | Castability (`canCast`), proposal reversal (`reverseProposedSpell`), ward (`beginWardsForTargets`), and cast/activation completion (`becomeCast`, `becomeActivated`, `beginActivationPayment`, `afterTargetsChosen`, `afterAdditionalCostAnnounced`, `afterModesChosen`). |
| `Choices.lean` | Sacrifice/discard/mode helper queries, behold, Riddles in the Dark (`applyRiddlesPiles`), and goad (`mustAttackIfAble`). |
| `Costs.lean` | Cost reductions (`applyCastCostReductions`, `playManaCost`, `activationManaCost`), `paySneak`, and `finishProposedSpell`. |
| `CastSpell.lean` | Initiating casts & announcing modes, X, loyalty, targets, and divided damage (`enterProposalWindow`, `castSpell`, `announceMode`, `payLoyaltyCost`, `announceX`, `announceTargetChoices`, `announceDividedDamage`). |
| `Activation.lean` | Activated ability legality and initiation (`validateActivation`, `canActivate`, `activateAbility`). |

### Layer 4: Effect, Ability, Trigger & Spell Resolution
| Module | Key Responsibilities |
| --- | --- |
| `SacrificeDiscard.lean` | `beginSacrificeCreatures`, `beginDiscardCards`, `applyConnive`, `sacrificeForActivation`. |
| `Damage.lean` | `destroyPermanent`, `markDamageOn`, `replacedDamageAmount`, `gainLife`, `loseLife`, `dealDamageFrom`, `dealDamageToPlayer`, `dealDamageToTarget`, `fightCreatures`. |
| `Pumps.lean` | `pumpPermanent`, `setUntilEotForm`, `addCounters`, `amass`. |
| `LibrarySearch.lean` | `beginLibrarySearch`, `finishLibrarySearch`, `placeSearched`, `shuffleThen`. |
| `ResolutionHelpers.lean` | Target legality wrappers (`withLegal*`), `applyPermanentAction`, `applyOnPermanent`, `beginSurveil`, `mill`. |
| `ResolutionEffects.lean` | `copyStackSpell`, `castAsPartOfResolution`, `counterStackSpell`, `exileUntilSourceLeaves`, `putReflexiveTrigger`, `resolveModeledReflexive`, `becomeCopyOf`, `copyStackAbility`, `beginUnlessPays`, `exileThenReturn`. |
| `ModeledTriggers.lean` | Shared trigger and spell resolution helpers (`applyBecomeCopy`, `applyEnterMod`, `offerVisionModes`, `offerHydeChoice`, `beginUnlessPays`, `exileThenReturn`, etc.). |
| `FraHelpers.lean` | Target slot legality, `beginFraChoice`, `discardFromHand`, `removeUpToCountersFrom`. |
| `FraResolve.lean` | Reality Fracture and Reality Fracture Commander (`Resolution.isFra`) resolver (`applyFra`, `applyDelayedSynthetic`). |
| `EffectResolution.lean` | Unified `Effect` interpreter (`applyUnified`, with thin wrappers `applyEffect`, `applyUnifiedAbility`, and `applyAbilityEffect`), plus `flushUnlessPays`. |
| `CastExtras.lean` | Kicker/morph/impending (`announceKicker`), gift (`announceGift`), teamwork (`announceTeamwork`, `payTeamworkCreatures`), cascade (`resolveCascade`), and The Ring (`temptWithTheRing`, `announceRingBearer`). |
| `TriggerArgs.lean` | Compositional selector evaluators (`TriggerRead`, `permanentsNamed`, `controllersNamed`, `collectPlayers`, `countNamed`, `triggerInt`, `triggerCount`). |
| `TriggeredAbilities.lean` | Compositional `TriggerResolution` handlers (`applyTriggerPump`, `applyTriggerDamage`, `applyPutCounters`, etc.), `interveningStillHolds` (CR 603.4), `applyTriggeredAbility`, `resumeTriggerSequence`, `chooseTriggerOr`, `putAttackTriggersOnStack`, `putBlockedTriggersOnStack`. |
| `SpellResolution.lean` | Top-of-stack resolution (`resolveTop`), Aura attachment (`resolveAuraSpell`), Adventure exile (`resolveAdventureSpell`), and CR 608.2b target checks (`fraAbilityTargetsAllIllegal`). |

### Layer 5: Combat, Turn Structure, Decisions & Top-Level Dispatch
| Module | Key Responsibilities |
| --- | --- |
| `Combat.lean` | `declareAttackers`, `declareBlockers`, `defaultCombatAssignment`, `dealAssignedCombatDamage`, `beginCombatDamageAssignment`, `announceCombatDamage`, `clearCombat`. |
| `Turns.lean` | Cleanup/EOT clearing (`clearEOT`, `discardToMaxHandSize`, `clearTurnActivations`), `startNextTurn`, `beginStep`, `beginTurn`, `advanceStep`. |
| `PriorityActions.lean` | `pay`, `announceAdditionalCost`, `pass`, `concede`. |
| `Mulligans.lean` | London mulligan loop and opening-hand actions (`openingHandsPending`, `beginMulliganRound`, `executeMulliganQueue`, `afterDeclaration`, `afterBottom`). |
| `Decisions.lean` | Handlers for top-level `Pending` choices (`finishScry`, `finishSurveil`, `convoke`, `finishProliferate`, `discardForDraw`, `payGeneric`, `acceptMay`, `chooseSpellOr`, `choosePermanents`, `decline`, `keepOpeningHand`, `keepLegend`, `stackTriggers`, `takeMulligan`, `putCardsOnBottom`, `supplyOrder`, `supplyIndex`). |
| `FraChoices.lean` | Handler (`answerFraChoice`) and heuristic default generator (`defaultFraAction`) for `Pending.fraChoice`. |
| `Actions.lean` | Top-level action entry points (`applyAction`, `apply`, `actor`). |
| `Start.lean` | Game initialization (`Start.materializeSeat`, `Start.start`). |
| `Mtg/Engine/Game.lean` | Re-exports `Mtg.Engine.Game.*` and provides test/simulation helpers (`mustApply`, `applyIdle`, `skipTo`, `skipToPending`, `passBoth`). |

---

## 2. Turn, Priority & Action Loop

```
g.apply p action (Actions.lean:104)
  │
  ├─► applyAction p action (Actions.lean:13)
  ├─► flushTokenEnters (Entering.lean:618 — queues ETB triggers for created tokens)
  ├─► if g.pending == .none:
  │     └─► g.receivePriority p (Triggers.lean:782)
  │           ├─► g.checkSBA (StateBasedActions.lean:271 — loops CR 704 SBAs)
  │           │     └─► may pause on Pending.chooseLegend (CR 704.5j)
  │           └─► Flushes g.waitingTriggers in APNAP order (CR 603.3b):
  │                 ├─► If a player has ≥2 waiting triggers from distinct sources:
  │                 │     pauses on Pending.chooseTriggerToStack
  │                 └─► Otherwise calls putTriggeredAbilityOnStack:
  │                       └─► may pause on Pending.fraChoice (.triggerModes ...)
  │                           or Pending.chooseTargets
  └─► flushUnlessPays (EffectResolution.lean:1475)
```

When all living players pass priority in succession (`consecutivePasses >= g.livingPlayers.size` in `PriorityActions.pass`):
- If `!g.stack.isEmpty`: calls `g.resolveTop.flushTokenEnters` (`SpellResolution.lean:69`), and if `g.pending == .none`, grants priority to `g.activePlayer` via `receivePriority`.
- If `g.stack.isEmpty`: advances the turn step via `g.advanceStep` (`Turns.lean:468`).

---

## 3. Spell Casting & Ability Activation Lifecycle (CR 601.2 / 602.2)

Casting a spell (`CastSpell.castSpell`) or activating a non-mana ability (`Activation.activateAbility`) creates a `ProposedSpell` (`Stack.lean:53`) on `g.proposedSpell : Option ProposedSpell`. `ProposedSpell` snapshots the game state before the proposal (`savedObjects`, `savedHand`, `savedGraveyard`, `savedExile`, `savedLibrary`, `savedStack`, `savedManaPool`, `savedLife`, `savedNextId`) so illegal proposals can be cleanly reversed by `Casting.reverseProposedSpell` (CR 733.1).

The proposal advances through these stages (pausing on `g.pending` whenever player input is required):
1. **Mode Announcement (CR 601.2b / 700.2)**: `Pending.chooseMode` → `CastSpell.announceMode` → `Casting.afterModesChosen`.
2. **X Value Announcement (CR 107.3a / 601.2b)**: `Pending.chooseX` → `CastSpell.announceX`.
3. **Additional / Optional Costs (CR 601.2b)**: `Pending.chooseKicker`, `Pending.chooseGift`, `Pending.chooseTeamwork`, `Pending.chooseAdditionalCost` → `Casting.afterAdditionalCostAnnounced`.
4. **Target Announcement & Divided Damage (CR 601.2c–d)**: `Pending.chooseTargets` → `CastSpell.announceTargetChoices` / `announceDividedDamage` → `Casting.afterTargetsChosen`.
5. **Cost Determination & Payment Window (CR 601.2f–h)**:
   - Cost reductions applied via `Costs.applyCastCostReductions`.
   - If the player must activate mana abilities, convoke, improvise, delve, or sacrifice/discard to pay costs, pauses on `Pending.activateManaAbilities`, `Pending.sacrificePermanent`, `Pending.discardForAdditionalCost`, or `Pending.fraChoice (.costPicks ...)`.
   - Completed by `PriorityActions.pay` → `Costs.finishProposedSpell` → `Casting.becomeCast` (for spells, triggering `Entering.putCastTriggersOnStack` and `Casting.beginWardsForTargets`) or `Casting.becomeActivated` (for activated abilities).

---

## 4. Stack Resolution Pipelines (`SpellResolution.lean`)

When `SpellResolution.resolveTop` (`Mtg/Engine/Game/SpellResolution.lean:69`) pops the top `StackEntry`, it dispatches to one of three execution pipelines depending on the stack object:

```
resolveTop (SpellResolution.lean:69)
  │
  ├─► 1. Activated Ability (or Modal Trigger with combined abilityEffect)
  │      `obj.abilityEffect = some e`
  │      └─► EffectResolution.applyUnifiedAbility (EffectResolution.lean:1597)
  │            ├─► applyFraResolution? (L59) ──► FraResolve.applyFra
  │            │                                   ├─► FrcResolve.applyFrc (for .frc e)
  │            │                                   └─► FraAbilities.applyFraAbility
  │            ├─► Ability-specific Resolution arms
  │            └─► Delegates to applyUnified via Resolution.toSpell
  │
  ├─► 2. Triggered Ability (including Saga Chapters & Reflexive Triggers)
  │      `obj.triggeredAbility = some t`
  │      └─► TriggeredAbilities.applyTriggeredAbility (TriggeredAbilities.lean:3777)
  │            ├─► Branch A: Compositional TriggerResolution (L3786–4593)
  │            │     Uses TriggerArgs.lean (permanentsNamed, collectPlayers, triggerInt, triggerCount)
  │            │     + pause-aware sequence runner (`triggerSequenceRest`)
  │            └─► Branch B: Effect.resolution fallback (L4594–4638)
  │                  Delegates to applyUnified / applyUnifiedAbility
  │
  └─► 3. Spell (Instant, Sorcery, or Permanent Spell)
         `obj.abilityEffect == none && obj.triggeredAbility == none`
         ├─► Instant / Sorcery / Adventure / Prepare spell:
         │     Resolves each chosen mode via EffectResolution.applyUnified (L847)
         │       ├─► applyFraResolution? (L59) ──► FraResolve.applyFra ──► FrcResolve.applyFrc
         │       └─► SpellResolution arms (L883–1471)
         └─► Permanent spell:
               resolveAuraSpell or putOntoBattlefield + afterPermanentEnters
```

---

## 5. Interactive Choices (`Pending` vs. `FraChoice`) & Continuations

### 5.1 Two-Tier `Pending` Sum Type (`Mtg/Engine/Game/Pending.lean`)
Because `Game` transitions are pure and synchronous, any effect that requires player input or external `--norandom` input sets `g.pending : Pending` and returns:
- **Top-level `Pending` (43 constructors, handled in `Decisions.lean`)**:
  - Turn/cast/combat prompts (`.declareAttackers`, `.declareBlockers`, `.assignCombatDamage`, `.activateManaAbilities`, `.chooseMode`, `.chooseX`, `.chooseTargets`, `.declareMulligan`, `.putOnBottom`, `.chooseLegend`, `.chooseTriggerToStack`, `.resolveRandom`) plus ~25 olderHOB/MSH prompts (`.scry`, `.surveil`, `.chooseSacrificeCreature`, `.chooseDiscardCard`, `.payOrLetCounter`, `.payWard`, `.chooseProliferate`, etc.).
- **Nested `Pending.fraChoice (player : PlayerId) (choice : FraChoice)` (74 constructors, handled in `FraChoices.lean`)**:
  - Used for newer interactive choices (library searches, modal trigger choices, crew, `costPicks`, cascade, Riddles in the Dark, Worlds Within Worlds, optional pay/sacrifice/discard/cast prompts).
  - `FraChoices.defaultFraAction` (`FraChoices.lean:1144`) computes deterministic default choices used by `Agent.choose` and `Game.applyIdle`.

### 5.2 Resuming Multi-Step Resolutions After a `Pending` Pause
1. **Pause-Aware Trigger Sequences (`g.triggerSequenceRest`)**:
   - When `applyTriggeredAbility` (`TriggeredAbilities.lean:3852–3907`) executes `.sequence rs`, it checks after each step whether `g.pending` became non-`.none`.
   - If a step paused for input, all remaining steps are saved in `g.triggerSequenceRest : Option TriggerSequenceRest`.
   - When the player answers the prompt in `Decisions.lean` or `FraChoices.lean`, the completion handler calls `g.resumeTriggerSequence` (`TriggeredAbilities.lean:4641`) to continue the remaining steps.
   - Optional `"You may ... If you do, ..."` trigger steps use `mayThenDrop`, `mayThenSkip`, `mayThenConditional`, and `mayThenResume` on `Game` (`Decisions.lean:268–298`).
2. **Ad-Hoc Spell/Ability Continuations on `Game`**:
   - Unlike `applyTriggeredAbility`, `applyUnified` and `applyUnifiedAbility` (`EffectResolution.lean:866, 1617`) currently fold over `.sequence` steps synchronously without checking `g.pending != .none`.
   - Consequently, multi-step spell/ability resolutions that pause mid-sequence rely on dedicated continuation fields on `Game` (`pendingDrawAfterScry`, `fraAfterLook : Option (PlayerId × Option ObjectId × Resolution)`, `palantirAfterScry`, `plusOneAfterSearch`, `plusOneAfterDiscards`, `unlessPaysInstead`, `chooseModesRest`). See [`docs/REFACTORING_AND_EXTENSION_GUIDE.md`](./REFACTORING_AND_EXTENSION_GUIDE.md) for how to unify this with `triggerSequenceRest`.
