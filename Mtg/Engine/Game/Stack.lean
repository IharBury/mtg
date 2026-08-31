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
inductive Target where
  | player (id : PlayerId)
  | permanent (id : ObjectId)
  /-- A card in a graveyard or a spell on the stack (CR 404 / 115.1). -/
  | card (id : ObjectId)
deriving DecidableEq, Repr, Inhabited, BEq

/-- A spell or ability on the stack (CR 405). Last array element is the top. -/
structure StackEntry where
  objectId : ObjectId
  controller : PlayerId
  targets : Array Target
  /-- Damage assigned to each target of a “divided as you choose” effect
  (CR 601.2d). Parallel to `targets`. -/
  dividedDamage : Array Nat := #[]
  /-- Set once targets (including choosing zero) have been announced
  (CR 603.3d / 601.2c). -/
  targetsAnnounced : Bool := false
  /-- Chosen mode index for a modal spell (CR 700.2). -/
  chosenMode : Option Nat := none
  /-- Optional “up to one” slots that were skipped while announcing
  (CR 115.1c / 601.2c). The current instance index is
  `targets.size + skippedOptionalSlots`. -/
  skippedOptionalSlots : Nat := 0
deriving Repr, Inhabited

/-- Whether a proposed payment is for a spell (CR 601) or an activated ability (CR 602). -/
inductive ProposalKind where
  | spell
  | activatedAbility
deriving DecidableEq, Repr, Inhabited, BEq

/-- Snapshot of a spell or activated ability whose total cost is being paid
(CR 601.2f–h / 602.2b). Used to reverse an illegal action (CR 733.1). -/
structure ProposedSpell where
  caster : PlayerId
  cost : ManaCost
  spellId : ObjectId
  original : GameObject
  handBefore : Array ObjectId
  stackBefore : Array StackEntry
  manaBefore : ManaPool
  tapped : Array ObjectId := #[]
  kind : ProposalKind := .spell
  /-- Source permanent of an activated ability; unused for spells. -/
  sourceId : Option ObjectId := none
  tapSource : Bool := false
  sacrificeSource : Bool := false
  /-- After mana is paid, the player must sacrifice an artifact or creature
  (another, when this is an activated ability). -/
  needsSacrificeOther : Bool := false
  /-- Life paid as part of the activation cost (CR 118.3b / 119.4). -/
  payLife : Nat := 0
  /-- Discard the source from hand as part of the activation cost (CR 702.29). -/
  discardSource : Bool := false
  /-- Modes of a modal activated ability, announced at CR 601.2b. -/
  abilityModes : Array Effect := #[]
  /-- Override the announced targeting shape (e.g. Equip Human). -/
  targetKindOverride : Option EffectTargetKind := none
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
  /-- Activated ability being paid, for extra costs. -/
  activation : Option ActivatedAbility := none
deriving Repr, Inhabited

end Mtg.Engine
