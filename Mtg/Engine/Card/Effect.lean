import Mtg.Engine.Card.SharedTrigger

/-!
# Unified one-shot effects (CR 608)

The `Effect` structure shared by spells, activated abilities, Saga
chapters, and triggered abilities, plus the shared `Resolution` vocabulary
they resolve through.
-/

namespace Mtg.Engine

/-- How an `Effect` resolves (CR 608). Shared shapes (`draw`, `scry`,
`onPermanent`, …) are used by spells, activated abilities, chapters, and
triggers. Family-specific leftovers stay nested so the C runtime tag stays
under the limit. -/
inductive Resolution where
  /-- Draw `n` cards. -/
  | draw (n : Nat)
  /-- Scry `n`. -/
  | scry (n : Nat)
  /-- Affect a still-legal permanent target. -/
  | onPermanent (action : PermanentAction)
  /-- Affect the source if it is still on the battlefield. -/
  | onSource (action : PermanentAction)
  /-- You gain `n` life. -/
  | gainLife (n : Nat)
  /-- Recruit. -/
  | recruit
  /-- Amass Goblins `n`. -/
  | amassGoblins (n : Nat)
  /-- Create `n` tokens of this kind. -/
  | createTokens (kind : TokenKind) (n : Nat) (tapped : Bool := false)
  /-- Add these mana types. -/
  | addMana (types : Array ManaType)
  /-- Discard `n` cards. -/
  | discard (n : Nat)
  /-- Apply each resolution in the given list, in order. -/
  | sequence (rs : List Resolution)
  /-- Spell-only resolution leftover. -/
  | spell (r : SpellResolution)
  /-- Activated-ability-only resolution leftover. -/
  | ability (r : AbilityResolution)
  /-- Trigger leftover (timing stays on the shared trigger effect). -/
  | trigger (e : SharedTrigger)
deriving Repr, Inhabited, BEq

/-- Unified one-shot effect for spells, activated abilities, Saga chapters,
and triggered abilities. Targeting, printed wording, and resolution live
here so Game has one apply path. -/
structure Effect where
  targeting : EffectTargeting := .of .none
  allowsZeroTargets : Bool := false
  maxTargets : Nat := 0
  dividedDamage : Option (Nat × Nat) := none
  spellCastKind : SpellCastKind := .extraLand
  abilityCastKind : AbilityCastKind := .other
  preferAsDefaultMode : Bool := false
  resolution : Resolution := .draw 0
  phrase : String := ""
deriving Repr, Inhabited, BEq

namespace Effect

/-- Whom this effect may target (CR 115.1 / 601.2c). -/
def targetKind (e : Effect) : EffectTargetKind :=
  e.targeting.kind

/-- How many targets must be announced (CR 601.2c). -/
def targetCount (e : Effect) : Nat :=
  e.targeting.targetCount

/-- True when announcing this effect requires choosing a target. -/
def requiresTarget (e : Effect) : Bool :=
  e.targeting.requiresTarget

/-- Upper bound on announced targets. `0` on `maxTargets` means `targetCount`. -/
def maxTargetCount (e : Effect) : Nat :=
  if e.maxTargets == 0 then e.targetCount else e.maxTargets

/-- Demonstration-agent category for a spell mode. -/
def castKind (e : Effect) : SpellCastKind :=
  e.spellCastKind

/-- Demonstration-agent category for an activated-ability mode. -/
def abilityKind (e : Effect) : AbilityCastKind :=
  e.abilityCastKind

/-- Recover the leftover spell resolution (common shapes lift back). -/
def spellResolution (e : Effect) : SpellResolution :=
  match e.resolution with
  | .spell r => r
  | .draw n => .draw n
  | .scry n => .scry n
  | .onPermanent a => .onPermanent a
  | .amassGoblins n => .amassGoblins n
  | .createTokens kind n _ => .createTokens kind n
  | .onSource a => .onPermanent a
  | .sequence rs =>
    match rs with
    | [.draw n, .discard 1] => .drawThenDiscard n
    | [.spell (.drawAndLoseLife 1 1), .amassGoblins n] => .drawLoseLifeThenAmass n
    | [.createTokens kind n _, .spell (.creaturesYouControlPump p t)] =>
      .createTokensThenTeamPump kind n p t
    | [.onPermanent .destroy, .gainLife n] => .destroyArtifactOrEnchantmentGainLife n
    | _ => .extraLand
  | .gainLife _ | .recruit | .addMana _ | .discard _ | .ability _ | .trigger _ =>
    .extraLand

/-- Recover the leftover activated-ability resolution. -/
def abilityResolution (e : Effect) : AbilityResolution :=
  match e.resolution with
  | .ability r => r
  | .draw n => .draw n
  | .scry n => .scry n
  | .onPermanent a => .onPermanent a
  | .onSource a => .onSource a
  | .gainLife n => .gainLife n
  | .recruit => .recruit
  | .createTokens kind n _ => .createTokens kind n
  | .addMana types => .addMana types
  | .sequence rs =>
    match rs with
    | [.draw n, .discard 1] => .drawThenDiscard n
    | [.onSource (.plusOne plus), .draw cards] => .plusOneAndDraw plus cards
    | [.onPermanent .destroy, .onSource (.plusOne 1)] => .destroyUpToOneThenPlusOne
    | [.onSource (.plusOne n), .createTokens kind 1 _] => .plusOneAndCreateTokens n kind
    | [.ability (.creaturesYouControlPump p t), .spell (.eachOpponentLosesLife life)] =>
      .creaturesYouControlGetOppsLoseLife p t life
    | _ => .draw 0
  | .amassGoblins _ | .discard _ | .spell _ | .trigger _ => .draw 0

/-- Recover a Saga chapter stored on this effect, if any. -/
def asChapter? (e : Effect) : Option ChapterResolution :=
  match e.resolution with
  | .trigger (.chapter _ ce) => some ce
  | _ => none

/-- Recover the leftover shared trigger stored on this effect, if any. -/
def asTrigger? (e : Effect) : Option SharedTrigger :=
  match e.resolution with
  | .trigger te => some te
  | _ => none

/-- Oracle-style reminder text. -/
def toNotation (e : Effect) : String :=
  e.phrase

instance : HasTargeting Effect where
  targeting e := e.targeting

instance : ToString Effect where
  toString := toNotation

end Effect

namespace Resolution

/-- Nested `sequence` constructors, left to right. -/
def flatten : Resolution → List Resolution
  | .sequence rs => rs.flatMap flatten
  | r => [r]

/-- Lift a spell resolution onto the shared `Resolution` vocabulary. -/
def ofSpell : SpellResolution → Resolution
  | .draw n => .draw n
  | .scry n => .scry n
  | .onPermanent a => .onPermanent a
  | .drawThenDiscard n => .sequence [.draw n, .discard 1]
  | .amassGoblins n => .amassGoblins n
  | .createTokens kind n => .createTokens kind n
  | .drawLoseLifeThenAmass n =>
    .sequence [.spell (.drawAndLoseLife 1 1), .amassGoblins n]
  | .createTokensThenTeamPump kind n p t =>
    .sequence [.createTokens kind n, .spell (.creaturesYouControlPump p t)]
  | .destroyArtifactOrEnchantmentGainLife n =>
    .sequence [.onPermanent .destroy, .gainLife n]
  | r => .spell r

/-- Lift an activated-ability resolution onto the shared `Resolution` vocabulary. -/
def ofAbility : AbilityResolution → Resolution
  | .draw n => .draw n
  | .scry n => .scry n
  | .onPermanent a => .onPermanent a
  | .onSource a => .onSource a
  | .gainLife n => .gainLife n
  | .recruit => .recruit
  | .drawThenDiscard n => .sequence [.draw n, .discard 1]
  | .createTokens kind n => .createTokens kind n
  | .addMana types => .addMana types
  | .plusOneAndDraw plus cards =>
    .sequence [.onSource (.plusOne plus), .draw cards]
  | .destroyUpToOneThenPlusOne =>
    .sequence [.onPermanent .destroy, .onSource (.plusOne 1)]
  | .plusOneAndCreateTokens n kind =>
    .sequence [.onSource (.plusOne n), .createTokens kind 1]
  | .creaturesYouControlGetOppsLoseLife p t life =>
    .sequence
      [.ability (.creaturesYouControlPump p t), .spell (.eachOpponentLosesLife life)]
  | r => .ability r

/-- Store a shared trigger on `Resolution`. Timing stays on the nested
effect so leftover family events remain recoverable. -/
def ofSharedTrigger (e : SharedTrigger) : Resolution :=
  .trigger e

end Resolution

end Mtg.Engine
