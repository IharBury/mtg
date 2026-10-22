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

/-- Rollback snapshot of the game state before a spell or activated ability
was proposed (CR 733.1). -/
structure ProposalSnapshot where
  original : GameObject
  handBefore : Array ObjectId
  stackBefore : Array StackEntry
  manaBefore : ManaPool
  tapped : Array ObjectId := #[]
deriving Repr, Inhabited

/-- Additional and alternative cost flags announced or awaiting payment on a
proposed spell or activated ability (CR 601.2b–f / 602.2b). -/
structure ProposedAdditionalCosts where
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
deriving Repr, Inhabited, BEq, DecidableEq

/-- Snapshot of a spell or activated ability whose total cost is being paid
(CR 601.2f–h / 602.2b). Used to reverse an illegal action (CR 733.1). -/
structure ProposedSpell extends ProposalSnapshot, ProposedAdditionalCosts where
  caster : PlayerId
  cost : ManaCost
  spellId : ObjectId
  kind : ProposalKind := .spell
  /-- Source permanent of an activated ability; unused for spells. -/
  sourceId : Option ObjectId := none
  /-- Modes of a modal activated ability, announced at CR 601.2b. -/
  abilityModes : Array Effect := #[]
  /-- Override the announced targeting shape (e.g. Equip Human). -/
  targetKindOverride : Option EffectTargetKind := none
  /-- Activated ability being paid, for extra costs. -/
  activation : Option ActivatedAbility := none
deriving Repr, Inhabited

end Mtg.Engine
