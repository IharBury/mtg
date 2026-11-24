import Mtg.Engine.Game.ModeledTriggers

/-!
# Reality Fracture resolution helpers

Shared helpers for resolving activated and loyalty abilities: target legality, sources and
causes of resolving abilities, reflexive triggers, and searches.
-/

namespace Mtg.Engine
namespace Game

/-- Whether `t` is still a legal target for the `i`th instance of “target”
of `spec` (CR 608.2b), accounting for `g.resolvingSkippedSlots` when optional
slots were skipped at announcement. -/
def targetLegalAt (g : Game) (controller : PlayerId) (spec : TargetSpec) (i : Nat)
    (t : Target) (sourceId : Option ObjectId) : Bool :=
  let pos :=
    if g.resolvingSkippedSlots.isEmpty || !spec.isMultiSlot then i
    else Id.run do
      let mut s := 0
      let mut rem := i
      let total := spec.totalPositions
      while s < total do
        if g.resolvingSkippedSlots.contains s then
          s := s + 1
        else if rem == 0 then
          return s
        else
          rem := rem - 1
          s := s + 1
      return s
  let stackSelf := g.resolvingAbility.orElse (fun _ => g.resolvingSpell)
  (g.legalTargetsForSlot controller (spec.slotAtPos pos) sourceId stackSelf).contains t

/-- The source's name for damage logs. -/
def fraSourceName (g : Game) (sourceId : Option ObjectId) : String :=
  match g.resolvingSpell.bind g.findObject? with
  | some o => g.name o
  | none =>
    match sourceId.bind g.findObject? with
    | some o => g.name o
    | none =>
      ((sourceId.bind g.damageSourceById?).map g.name).orElse
        (fun _ => (sourceId.bind g.lastKnownBefore?).map (·.name))
        |>.getD "The effect"

/-- Grant `k` to `o` until end of turn, logged. -/
def grantKeywordsUntilEot (g : Game) (o : GameObject) (k : Array KeywordAbility) : Game :=
  if k.isEmpty then g else g.grantUntilEotLogged o k

/-- The creature type `p` chooses for “choose a creature type”: the type most
common among creatures they control. -/
def chooseCreatureTypeFor (g : Game) (p : PlayerId) : CardSubtype :=
  let counts : Array (CardSubtype × Nat) :=
    (g.creaturesControlledBy p).foldl (fun acc o =>
      (g.subtypes o).foldl (fun acc t =>
        if !t.isCreatureType then acc
        else
          match acc.findIdx? (·.1 == t) with
          | some i => acc.modify i (fun (s, n) => (s, n + 1))
          | none => acc.push (t, 1)) acc) #[]
  (counts.foldl (fun best c =>
    match best with
    | none => some c
    | some b => if c.2 > b.2 then some c else best) none).map (·.1) |>.getD .human

/-- Cards in `p`'s hand that a “reveal your hand, you choose” effect may pick. -/
def revealedHandChoices (g : Game) (p : PlayerId) (permanentOnly : Bool) : Array ObjectId :=
  (g.player p).hand.filter (fun id =>
    match g.findObject? id with
    | some o =>
      !g.isLand o && (!permanentOnly || g.isPermanentCard o)
    | none => false)

/-- `victim` reveals their hand and `chooser` picks a card for them to discard. -/
def beginRevealDiscard (g : Game) (chooser victim : PlayerId) (permanentOnly : Bool) : Game :=
  let g := g.revealHand victim
  if (g.revealedHandChoices victim permanentOnly).isEmpty then
    let what := if permanentOnly then "nonland permanent card" else "nonland card"
    g.logMsg s!"{(g.player victim).name} has no {what} to discard"
  else
    g.beginFraChoice chooser (.discardFromRevealedHand victim permanentOnly)
      s!"{(g.player chooser).name} chooses a card from {(g.player victim).name}'s hand"

/-- Cards `p` owns outside the game. -/
def outsideCards (g : Game) (p : PlayerId) : Array GameObject :=
  g.objects.filter (fun o => o.zone == .outside p)

/-- Give `p`'s sideboard cards object identities outside the game, so an
effect can reveal or move them (CR 400.11b). -/
def materializeSideboard (g : Game) (p : PlayerId) : Game :=
  let side := (g.player p).sideboard
  let g := g.changePlayer p (.sideboard #[])
  side.foldl (fun g card => (g.allocObject card p (.outside p)).1) g

/-- Cards named Sphinx's Approach in `p`'s graveyard. -/
def sphinxsApproachesInGraveyard (g : Game) (p : PlayerId) : Array ObjectId :=
  (g.player p).graveyard.filter (fun id =>
    (g.findObject? id).any (fun o => g.name o == "Sphinx's Approach"))

/-- The resolving activated or triggered ability's stack object. -/
def resolvingAbilityObject? (g : Game) : Option GameObject :=
  g.resolvingAbility.bind g.findObject?

end Game
end Mtg.Engine
