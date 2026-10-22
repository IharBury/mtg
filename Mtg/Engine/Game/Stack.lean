import Mtg.Engine.Game.Object

/-!
# Stack entries and proposed casts (CR 405 / 601)

`Target` (CR 115), `StackEntry` — a spell or ability on the stack — and
`ProposalKind` / `ProposedSpell`, the snapshot of a spell or activated
ability whose total cost is being determined and paid
(CR 601.2f–h / 602.2b), kept so an illegal proposal can be reversed
(CR 733.1).
-/

namespace Mtg.Engine

/-- A target chosen while casting a spell or putting an ability on the stack
(CR 115). -/
abbrev Target := PlayerId ⊕ (ObjectId × Bool)

namespace Target

/-- Unified target (CR 115): player (`.inl id`), permanent (`.inr (id, false)`), or card/spell (`.inr (id, true)`). -/
@[match_pattern] abbrev targetKind (k : PlayerId ⊕ (ObjectId × Bool)) : Target := k

@[match_pattern] abbrev player (id : PlayerId) : Target :=
  .inl id
@[match_pattern] abbrev permanent (id : ObjectId) : Target :=
  .inr (id, false)
/-- A card in a graveyard or a spell on the stack (CR 404 / 115.1). -/
@[match_pattern] abbrev card (id : ObjectId) : Target :=
  .inr (id, true)

end Target

/-- A spell or ability on the stack (CR 405), shared spell-resolution context
(`SpellResolutionContext`, CR 608.2c), or shared ability/choice resolution context
(`TriggerResolutionContext`, `TriggerSequenceRest`, `TriggerOrRest`, `ChooseModesRest`,
`TriggerRead`, `UnlessPaysRest`, `MayEffectRest`, `SpellOrRest`, CR 118.12 / 603.3 / 608.2).
Last array element is the top. -/
abbrev StackEntry := WaitingTrigger

/-- Whether a proposed payment is for a spell (CR 601) or an activated ability (CR 602). -/
abbrev ProposalKind := Target

namespace ProposalKind

@[match_pattern] abbrev proposalKind (isActivatedAbility : Bool := false) : ProposalKind :=
  .inr (⟨0⟩, isActivatedAbility)
@[match_pattern] abbrev spell : ProposalKind := .proposalKind false
@[match_pattern] abbrev activatedAbility : ProposalKind := .proposalKind true

end ProposalKind

namespace Target
export ProposalKind (proposalKind spell activatedAbility)
end Target

set_option maxHeartbeats 800000 in
/-- Snapshot of a spell or activated ability whose total cost is being paid
(CR 601.2f–h / 602.2b, used to reverse an illegal action under CR 733.1), or
cross-step resolution notes (`ResolutionNotes`, CR 608.2c / CR 608.2h). -/
structure ProposedSpell where
  original : GameObject := default
  handBefore : Array ObjectId := #[]
  stackBefore : Array StackEntry := #[]
  manaBefore : ManaPool := {}
  tapped : Array ObjectId := #[]
  tapSource : Bool := false
  sacrificeSource : Bool := false
  /-- After mana is paid, the player must sacrifice an artifact or creature
  (another, when this is an activated ability). -/
  needsSacrificeOther : Bool := false
  /-- After mana is paid, the player must discard a card as an additional
  cost (e.g. Titania). -/
  needsDiscardCard : Bool := false
  /-- Life paid as part of the activation cost (CR 118.3b / 119.4). -/
  payLife : Nat := 0
  /-- Discard the source from hand as part of the activation cost (CR 702.29). -/
  discardSource : Bool := false
  /-- The proposed spell will be kicked if this is true. -/
  kicked : Bool := false
  /-- Kicker has been announced (paid or declined). -/
  kickerAnnounced : Bool := false
  /-- Opponent chosen for a promised gift, if any. -/
  giftTo : Option PlayerId := none
  /-- Gift has been announced (promised or declined). -/
  giftAnnounced : Bool := false
  /-- The proposed spell will be cast using teamwork if this is true. -/
  teamworkPaid : Bool := false
  /-- Teamwork has been announced (paid or declined). -/
  teamworkAnnounced : Bool := false
  /-- The ability's cost is −X loyalty; X is announced before targets and
  the loyalty is paid then (CR 107.3 / 606.4). -/
  loyaltyX : Bool := false
  /-- X is the number of +1/+1 counters removed from the source as part of
  the cost (The Astonishing Ant-Man). -/
  removePlusOneX : Bool := false
  /-- The spell is cast for its sneak cost; this unblocked attacker returns
  to hand as the cost is paid (MSH sneak). -/
  sneakAttacker : Option ObjectId := none
  caster : PlayerId := ⟨0⟩
  cost : ManaCost := ManaCost.empty
  spellId : ObjectId := ⟨0⟩
  kind : ProposalKind := .spell
  /-- Source permanent of an activated ability; unused for spells. -/
  sourceId : Option ObjectId := none
  /-- Modes of a modal activated ability, announced at CR 601.2b. -/
  abilityModes : Array Effect := #[]
  /-- Override the announced targeting shape (e.g. Equip Human). -/
  targetKindOverride : Option EffectTargetKind := none
  /-- Activated ability being paid, for extra costs. -/
  activation : Option ActivatedAbility := none
  /-- Humans chosen for the current “tap any number of Humans” step.
  `.draw (amount := .forEachTappedHuman)` draws this many cards. -/
  humansTappedThisWay : Nat := 0
  /-- Permanents destroyed by `.destroy .oppArtifactsEnchantments (note := .countDestroyed)`.
  `.gainLife .forEachDestroyedThisWay` gains this much life. -/
  permanentsDestroyedThisWay : Nat := 0
  /-- Ordinal recorded by the current `noteResolveThisTurn` step.
  `«if» (.nthResolve _)` reads it and a finished sequence clears it. -/
  nthResolveThisWay : Option Nat := none
  /-- Excess damage noted by `dealDamage` with `.excess` for the following
  amass step. -/
  excessDamageThisWay : Nat := 0
  /-- Cards discarded by accepting `.discard .hand`. `none` means declined. -/
  handDiscardedThisWay : Option Nat := none
  /-- A count captured before a later step could change it (invasion counters,
  cards discarded). -/
  notedCountThisWay : Nat := 0
  /-- Power of the creature sacrificed for
  `putCounters .plusOneSacrificedPower`. -/
  sacrificedPowerThisWay : Option Nat := none
  /-- A hope counter was removed by the current `removeCounters .hope .source` step.
  `«if» .removedHope` draws a card when this is set. -/
  removedHopeThisWay : Bool := false
  /-- A permanent was returned to its owner's hand by the current
  `returnToHand` step when it notes `.returnedPermanent`.
  `«if» .returnedPermanent` puts a +1/+1 counter on the source when this is set. -/
  returnedPermanentThisWay : Bool := false
  /-- The current sequence step asked the rest of the sequence not to run
  (the source had already left, or no mana was spent). -/
  skipTriggerSequenceRest : Bool := false
  /-- `.mill` noted `.opponentsMilled`: an opponent milled at least one card. -/
  opponentsMilledThisWay : Bool := false
  /-- `sacrifice .you .plan .forReflexive` sacrificed the Plan. -/
  planWasSacrificed : Bool := false
  /-- `sacrifice .you .source .noted` sacrificed the source. -/
  sourceWasSacrificed : Bool := false
  /-- `.destroy .target (note := .forAmass)` chose a legal target. The controller,
  amount, and whether you controlled it feed the following amass and draw steps. -/
  destroyedForAmassThisWay : Bool := false
  amassControllerThisWay : Option PlayerId := none
  amassAmountThisWay : Nat := 0
  amassYouControlledThisWay : Bool := false
  /-- Palantír finished putting an influence counter; the following step offers
  the opponent's draw choice. Controller, opponent, and the Palantír. -/
  palantirChoiceReady : Option (PlayerId × PlayerId × ObjectId) := none
  /-- `revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer`
  stored the impulse. The following `.mayCast .impulse` offers the cast. -/
  grimaImpulseReady : Bool := false
  grimaImpulseVictim : Option PlayerId := none
  grimaImpulseFound : Option ObjectId := none
  grimaImpulseOthers : Array ObjectId := #[]
  /-- Card discarded while a later `.put .discardedLand (how := .tapped)`
  may put that land onto the battlefield tapped (Silvan Reveler). The
  player who discarded it, and the card. -/
  discardedCardThisWay : Option (PlayerId × ObjectId) := none
  /-- The permanent marked by the current `dealDamage` step when it notes
  `.markedPermanent`. `«if» (.dealtDamageToSubtype _)` destroys it when it
  has the subtype. -/
  permanentDealtDamageThisWay : Option ObjectId := none
  /-- Cards milled by `.mill` when it notes `.milledCards`. -/
  milledIdsThisWay : Array ObjectId := #[]
  /-- Cards `revealLibrary` just showed. A following step reads them. -/
  revealedIdsThisWay : Array ObjectId := #[]
  /-- Lands exiled by `exile .landsYouControl .forLater .lands`.
  `.put .notedLands (how := .tapped)` returns them. -/
  exiledIdsThisWay : Array ObjectId := #[]
  /-- Creature exiled by `exile .target .untilSourceLeaves .copyAndHost`, copied by the next step.
  The object is the one from before it moved. -/
  notedCopyObject : Option GameObject := none
  notedHostId : Option ObjectId := none
  /-- Source of the Balin ability, for the damage step after the discard. -/
  notedSourceThisWay : Option ObjectId := none
  /-- Creature that received Equipment from `attach .anyYouControl .target`. -/
  equipmentAttachedHost : Option ObjectId := none
  /-- Token created for the following attach or counter step. -/
  createdTokenThisWay : Option ObjectId := none
  /-- Artifact put from hand by `.put .artifactFromHand (note := .forAttach)`,
  and the creature `attach .putArtifact .notedHost` attaches it to when it
  is Equipment. -/
  putArtifactThisWay : Option (ObjectId × ObjectId) := none
  /-- Card exiled by `exile .graveyardCard .forLater .playCard`. -/
  playExiledThisWay : Option ObjectId := none
deriving Repr, Inhabited

end Mtg.Engine
