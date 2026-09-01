import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.SpellEffects
import Mtg.Engine.Mana
import Mtg.Engine.TypeLine

/-!
# Traditional card definitions

A printed card as a list of `CardPart`s: name, mana cost, type line,
abilities, and (for adventurer cards) an `alternative` face. Compiles to
`CardDef` so the engine and existing catalogs stay unchanged.
-/

namespace Mtg.Engine

/-- A keyword or other printed ability on a card or granted by an effect. -/
inductive Ability where
  | keyword : Keyword → Ability
deriving Repr, Inhabited, BEq

/-- Whom or what a spell or ability may target (CR 115.1). -/
inductive Filter where
  | and : Filter → Filter → Filter
  | any
  | cardType : CardType → Filter
  | or : Filter → Filter → Filter
  /-- Permanent the spell’s controller controls. -/
  | sameController
deriving Repr, Inhabited, BEq

namespace Filter

/-- `sameController` last so `and` matches do not restate both orders. -/
def normalize : Filter → Filter
  | .and .sameController f => .and (normalize f) .sameController
  | .and f .sameController => .and (normalize f) .sameController
  | .and a b => .and (normalize a) (normalize b)
  | .or a b =>
    let a := normalize a
    let b := normalize b
    match a, b with
    | .cardType .creature, .cardType .artifact => .or b a
    | _, _ => .or a b
  | f => f

/-- Compile a filter to a targeting shape the engine already understands. -/
def toTargetKind (f : Filter) : EffectTargetKind :=
  match normalize f with
  | .any => .permanent
  | .cardType .creature => .creature
  | .cardType .artifact => .artifact
  | .and (.cardType .creature) .sameController => .creatureYouControl
  | .and (.cardType .artifact) .sameController => .artifactYouControl
  | .and (.or (.cardType .artifact) (.cardType .creature)) .sameController =>
    .artifactOrCreatureYouControl
  | _ => .permanent

end Filter

/-- How many objects matching `filter` a spell or ability may target. -/
structure TargetSelector where
  minimumTargets : Nat := 1
  maximumTargets : Nat := 1
  filter : Filter := .any
deriving Repr, Inhabited, BEq

namespace TargetSelector

def toTargeting (s : TargetSelector) : EffectTargeting :=
  .of s.filter.toTargetKind

end TargetSelector

/-- When a continuous effect ends. -/
inductive Trigger where
  | endOfGame
  | endOfTurn
deriving Repr, Inhabited, BEq

/-- A continuous effect granted by a spell or ability. -/
inductive ContinuousEffect where
  | gainAbility : Ability → ContinuousEffect
deriving Repr, Inhabited, BEq

/-- What a spell or ability does. `CardAction` is the printed-card name for
this tree; player input uses `Action` in `Game`. -/
inductive CardAction where
  | continuous : List ContinuousEffect → Trigger → CardAction
  | targeted : TargetSelector → CardAction → CardAction
deriving Repr, Inhabited, BEq

namespace CardAction

/-- Until-end-of-turn keyword grants implied by `continuous` effects. -/
def grantedKeywords : List ContinuousEffect → Keywords
  | [] => Keywords.none
  | .gainAbility (.keyword k) :: rest =>
    k.toKeywords.merge (grantedKeywords rest)

/-- Compile to the unified `Effect` the engine resolves. Targeting is applied
before `mkSpell` so the printed phrase names the same noun as a hand-written
`Effect`. -/
def toEffect : CardAction → Effect
  | .continuous effects _duration =>
    Effect.mkSpell (.of .none) (.onPermanent (.grantKeywords (grantedKeywords effects)))
      (castKind := .pump)
  | .targeted sel (.continuous effects _duration) =>
    Effect.mkSpell sel.toTargeting (.onPermanent (.grantKeywords (grantedKeywords effects)))
      (castKind := .pump)
      (maxTargets := if sel.maximumTargets ≤ 1 then 0 else sel.maximumTargets)
      (allowsZeroTargets := sel.minimumTargets == 0)
  | .targeted sel inner =>
    let e := inner.toEffect
    { e with
      targeting := sel.toTargeting
      maxTargets :=
        if sel.maximumTargets ≤ 1 then e.maxTargets else sel.maximumTargets
      allowsZeroTargets := e.allowsZeroTargets || sel.minimumTargets == 0 }

end CardAction

/-- One printed characteristic or ability of a card face. -/
inductive CardPart where
  | name : String → CardPart
  /-- Printed symbols; `ManaCost` is the engine structure, this list is the
  prototype spelling (`.manaCost [.mono .white]`). -/
  | manaCost : List ManaSymbol → CardPart
  | type : CardType → CardPart
  | supertype : CardSupertype → CardPart
  | subtype : CardSubtype → CardPart
  | power : Nat → CardPart
  | toughness : Nat → CardPart
  | ability : Ability → CardPart
  | alternative : List CardPart → CardPart
  | action : CardAction → CardPart
deriving Repr, Inhabited, BEq

/-- A traditional (non-token, non-DFC-only) printed card. -/
inductive TraditionalCardDefinition where
  | card : List CardPart → TraditionalCardDefinition
deriving Repr, Inhabited, BEq

/-- Accumulator for one face of a `TraditionalCardDefinition`. -/
structure CardFace where
  name : String := ""
  manaCost : ManaCost := ManaCost.empty
  types : Array CardType := #[]
  supertypes : Array Supertype := #[]
  subtypes : Array Subtype := #[]
  power : Option Int := none
  toughness : Option Int := none
  keywords : Keywords := Keywords.none
  action : Option CardAction := none
  alternatives : Array (List CardPart) := #[]
deriving Inhabited

namespace CardFace

def apply (b : CardFace) : CardPart → CardFace
  | .name n => { b with name := n }
  | .manaCost c => { b with manaCost := (c : ManaCost) }
  | .type t => { b with types := b.types.push t }
  | .supertype s => { b with supertypes := b.supertypes.push s }
  | .subtype s => { b with subtypes := b.subtypes.push s.toString }
  | .power n => { b with power := some n }
  | .toughness n => { b with toughness := some n }
  | .ability (.keyword k) => { b with keywords := b.keywords.merge k.toKeywords }
  | .alternative parts => { b with alternatives := b.alternatives.push parts }
  | .action a => { b with action := some a }

def ofParts (parts : List CardPart) : CardFace :=
  parts.foldl apply {}

def toAdventure (b : CardFace) : AdventureFace := {
  name := b.name
  manaCost := b.manaCost
  types := if b.types.isEmpty then #[.sorcery] else b.types
  subtypes := if b.subtypes.isEmpty then #["Adventure"] else b.subtypes
  oracleText :=
    match b.action with
    | some a => a.toEffect.phrase
    | none => ""
  spellEffect := b.action.map (·.toEffect)
}

end CardFace

namespace TraditionalCardDefinition

/-- Compile printed parts to the engine `CardDef`. When `oracleText` is
omitted, keywords and the Adventure face are reconstructed so the card
still has ability text. -/
def toCardDef (d : TraditionalCardDefinition) (oracleText : String := "") : CardDef :=
  match d with
  | .card parts =>
    let b := CardFace.ofParts parts
    let adventure :=
      match b.alternatives[0]? with
      | some alt => some (CardFace.ofParts alt).toAdventure
      | none => none
    let generated :=
      let kw :=
        let s := toString b.keywords
        if s.isEmpty then [] else [s]
      let adv :=
        match adventure with
        | none => []
        | some a =>
          let typeLine := formatTypeLine #[] a.types a.subtypes
          let effect :=
            match a.spellEffect with
            | some e => e.phrase
            | none => a.oracleText
          ["//ADV//", s!"{a.name} {a.manaCost}", typeLine, effect]
      String.intercalate "\n" (kw ++ adv)
    {
      name := b.name
      manaCost := b.manaCost
      types := b.types
      subtypes := b.subtypes
      supertypes := b.supertypes
      power := b.power
      toughness := b.toughness
      keywords := b.keywords
      spellEffect := b.action.map (·.toEffect)
      adventure := adventure
      oracleText := if oracleText.isEmpty then generated else oracleText
    }

instance : Coe TraditionalCardDefinition CardDef where
  coe d := d.toCardDef

end TraditionalCardDefinition

-- Concerted Care: target artifact or creature you control gains hexproof
-- and indestructible until end of turn.
#guard
  let action : CardAction :=
    .targeted
      ({filter := .and
         (.or
           (.cardType .artifact)
           (.cardType .creature))
         .sameController})
      (.continuous
        [
          .gainAbility (.keyword .hexproof),
          .gainAbility (.keyword .indestructible)]
        .endOfTurn)
  action.toEffect == Effect.grantHexproofIndestructible

#guard Filter.toTargetKind
  (.and (.or (.cardType .artifact) (.cardType .creature)) .sameController)
  == .artifactOrCreatureYouControl

#guard Filter.toTargetKind
  (.and .sameController (.or (.cardType .creature) (.cardType .artifact)))
  == .artifactOrCreatureYouControl

end Mtg.Engine
