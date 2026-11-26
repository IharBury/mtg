import Mtg.Engine.Game.StateBasedActions

/-!
# Priority and play timing (CR 117 / 116.2a)

Multiplayer flags, who has priority, sorcery-speed checks, land-play
allowances (CR 305.2b), and permission to play cards from exile, the
graveyard, or the top of the library (CR 118.14 / 400.7).
-/

namespace Mtg.Engine
namespace Game

/-- CR 100.1b: a multiplayer game begins with more than two players. -/
def isMultiplayer (g : Game) : Bool :=
  g.players.size > 2

/-- CR 103.8a–c / 810.6: in a two-player game or a two-team Two-Headed Giant
game, the starting player or starting team skips the draw step of their first
turn. Multiplayer games with more than two teams/sides do not skip that draw
(CR 103.8c). -/
def skipsFirstDraw (g : Game) : Bool :=
  let teamCount := (g.players.foldl (fun (reps : Array PlayerId) pl =>
    if reps.any (fun r => r == pl.id || g.areTeammates r pl.id) then reps
    else reps.push pl.id) #[]).size
  if teamCount > 2 then false
  else
    let sp := g.startingPlayer
    if g.activePlayer == sp then
      g.isFirstTurn
    else if g.areTeammates sp g.activePlayer then
      let (ok, seen) := g.events.foldl (fun (ok, seen) ev =>
        match ev.change with
        | .engine (.startingPlayer _) => (true, (#[] : Array PlayerId))
        | .rules (.turn (.turnBegan q extra)) =>
          if ok && !extra && g.areTeammates sp q && !seen.contains q then
            (true, seen.push q)
          else
            (false, seen)
        | _ => (ok, seen)) (true, (#[] : Array PlayerId))
      ok && !seen.isEmpty
    else false

/-- Whether a player currently receives priority (CR 117.3a, 502.4, 514.3,
103.8a / 500.11). A skipped draw step grants none. -/
def playersReceivePriority (g : Game) : Bool :=
  if g.step == .cleanup then g.cleanupGivesPriority
  else if g.step == .draw && g.skipsFirstDraw then false
  else g.step.playersReceivePriority

def asSorcery? (g : Game) (p : PlayerId) : Bool :=
  !g.over && g.pending == .none && g.stack.isEmpty &&
  g.step.isMainPhase && g.activePlayer == p && g.priority == p

/-- True while a spell with split second is on the stack (CR 702.61a): either printed
`Keyword.splitSecond` or granted in Layer 6 by a battlefield permanent (Samut). -/
def splitSecondOnStack (g : Game) : Bool :=
  g.stack.any (fun e =>
    match g.findObject? e.objectId with
    | some o =>
      o.abilityEffect.isNone && o.triggeredAbility.isNone && g.hasSplitSecond o
    | none => false)

/-- Yuriko, Blade of the Mighty: during combat, players can't cast spells or
activate abilities that aren't mana abilities. -/
def combatLocksNonManaAbilities (g : Game) : Bool :=
  (g.step == .beginningOfCombat || g.step == .declareAttackers ||
    g.step == .declareBlockers || g.step == .combatDamage || g.step == .endOfCombat) &&
    g.battlefield.any (fun x =>
      let xCtrl := g.controllerOf x |>.getD x.owner
      (g.staticAbilities x).any fun ab =>
        ab.anyRule fun cond? r =>
          cond?.all (EvalExpr.evalCondition g { controller := xCtrl, sourceId := some x.id }) &&
            match r with
            | .game (.lockNonManaDuringPhase .combat _) => true
            | _ => false)

/-- Loyalty counters among Jace planeswalkers `p` controls. -/
def jaceLoyaltyAmong (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).foldl (fun acc o =>
    if g.isPlaneswalker o && g.hasSubtype o .jace then acc + o.status.loyaltyCounters
    else acc) 0

/-- Whether `ab`'s cost requires its source to be a permanent on the battlefield
(CR 113.6 / 602.2b). -/
def _root_.Mtg.Engine.ActivatedAbility.needsBattlefieldSource (ab : ActivatedAbility) : Bool :=
  ab.cost.tap || ab.cost.untap || ab.cost.sacrificeSource ||
    ab.cost.sacrificeEquipmentAttachedToSource ||
    ab.cost.isLoyalty ||
    ab.cost.removeStoryCounter || ab.cost.removeIndestructibleCounter ||
    ab.cost.removeAnyNumberPlusOne || ab.cost.putStunCounterOnSource ||
    ab.cost.exileSourceFromBattlefield || ab.cost.crewPower?.isSome ||
    ab.cost.exileManaSymbols?.isSome

/-- Mana abilities (CR 605.1a, 25 September 2026): an activated ability is a
mana ability iff it satisfies all four CR 605.1a criteria (`ab.isManaAbility`). -/
def isManaActivation (ab : ActivatedAbility) : Bool :=
  ab.isManaAbility

def hasPriority (g : Game) (p : PlayerId) : Bool :=
  !g.over && g.pending == .none && g.priority == p && g.playersReceivePriority

/-- Extra land plays from permanents such as Thranduil's Company (CR 305.2). Each such
permanent is cumulative with other extra-land effects (rulings 288 / 306). -/
def extraLandsFromPermanents (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).foldl (fun acc o =>
    let env : EvalEnv := { controller := p, sourceId := some o.id }
    (g.staticAbilities o).foldl (fun a ab =>
      match ab with
      | .ruleModifying cond? rule =>
        if cond?.all (EvalExpr.evalCondition g env) then
          rule.flatten.foldl (fun n r =>
            match r with
            | .player (.additionalLands who cnt) =>
              if EvalExpr.matchesPlayerFilter g env who p then n + cnt else n
            | _ => n) a
        else a
      | _ => a) acc) 0

/-- How many lands `p` may play this turn (CR 305.2 / 305.2b). -/
def landPlaysAllowed (g : Game) (p : PlayerId) : Nat :=
  1 + g.additionalLandsThisTurn p + g.extraLandsFromPermanents p

/-- Lands remaining this turn (CR 305.2 / 305.3 / 116.2a). -/
def canPlayLand (g : Game) (p : PlayerId) : Bool :=
  g.asSorcery? p && g.loggedLandsPlayed p < g.landPlaysAllowed p

/-- Whether `p` may play `o` from exile under a granted permission (CR 701.18 / 715.3d). -/
def mayPlayFromExile (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.zone == .exile &&
  match g.playPermissionFor? p o with
  | some perm =>
    -- Ruling 744: only the current controller of the prepared permanent may
    -- cast the copy of its prepare spell.
    let mayCast :=
      match perm.prepareSource with
      | some src =>
        match g.findObject? src with
        | some perm => perm.isOnBattlefield && perm.status.prepared && g.controlledBy perm p
        | none => false
      | none => perm.player == p
    mayCast &&
      (match perm.requireSubtype with
       | none => true
       | some t => g.controlsAnySubtype p #[t])
  | none => false

/-- Cards in exile that `p` currently may play. -/
def exiledPlayable (g : Game) (p : PlayerId) : Array GameObject :=
  g.objects.filter (fun o => g.mayPlayFromExile p o || g.mayCastExiledBySource p o)

/-- Mole Man lets you play land cards from your graveyard (MSH 253 / 254).
Cycling and other activated abilities of those cards are still illegal. -/
def controlsPlayLandsFromGraveyard (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any fun x =>
    let env : EvalEnv := { controller := p, sourceId := some x.id }
    (g.staticAbilities x).any fun ab =>
      ab.anyRule fun cond? r =>
        cond?.all (EvalExpr.evalCondition g env) &&
          match r with
          | .play (.mayPlayFrom who .graveyard (.hasType .land) true false _ _) =>
            EvalExpr.matchesPlayerFilter g env who p
          | _ => false

def mayPlayFromGraveyard (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.zone == .graveyard p && o.owner == p && isDiscardableCard o &&
    ((g.baseCard o).flashback.isSome || g.flashbackUntilEot o ||
      (g.isLand o && g.controlsPlayLandsFromGraveyard p))

/-- True when `p` controls a permanent that lets them look at the library top. -/
def controlsLookAtTop (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any fun o =>
    let env : EvalEnv := { controller := p, sourceId := some o.id }
    (g.staticAbilities o).any fun ab =>
      ab.anyRule fun cond? r =>
        cond?.all (EvalExpr.evalCondition g env) &&
          match r with
          | .play (.lookAtTopOfLibrary who) => EvalExpr.matchesPlayerFilter g env who p
          | _ => false

/-- True when `p` may look at the top card of their library right now.
Elven Chorus does not reveal a new top while a spell from that top is
still being cast. -/
def canLookAtLibraryTop (g : Game) (p : PlayerId) : Bool :=
  g.controlsLookAtTop p && !g.castingFromTop

/-- True when `p` controls a permanent that lets them cast creatures from
the top of their library. Does not grant flash or change timing. -/
def controlsCastCreaturesFromTop (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any fun o =>
    let env : EvalEnv := { controller := p, sourceId := some o.id }
    (g.staticAbilities o).any fun ab =>
      ab.anyRule fun cond? r =>
        cond?.all (EvalExpr.evalCondition g env) &&
          match r with
          | .play (.mayPlayFrom who .library (.hasType .creature) false false _ _) =>
            EvalExpr.matchesPlayerFilter g env who p
          | _ => false

/-- True when `o` is the top card of `p`'s library and they may cast it as
a creature spell from there. Timing is still checked by `canCast`. -/
def controlsPlayLandsFromTop (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any fun o =>
    let env : EvalEnv := { controller := p, sourceId := some o.id }
    (g.staticAbilities o).any fun ab =>
      ab.anyRule fun cond? r =>
        cond?.all (EvalExpr.evalCondition g env) &&
          match r with
          | .play (.mayPlayFrom who .library (.hasType .land) true false _ _) =>
            EvalExpr.matchesPlayerFilter g env who p
          | _ => false

def mayPlayFromLibraryTop (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.zone == .library p &&
    (g.player p).library.back? == some o.id &&
    (((g.isCreature o || (g.baseCard o).morph.isSome) && g.controlsCastCreaturesFromTop p) ||
      (g.isLand o && g.controlsPlayLandsFromTop p))

/-- Whether `p` may play `o` as a land from exile under a non-cast-only permission (CR 305.9). -/
def mayPlayLandFromExile (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.zone == .exile &&
    (g.playPermissionsFor p o).any fun perm =>
      perm.player == p &&
        perm.landsAllowed &&
        !perm.fromAdventure &&
        !perm.withoutManaCost &&
        !perm.payLifeEqualManaValue &&
        perm.prepareSource.isNone &&
        match perm.requireSubtype with
        | none => true
        | some t => g.controlsAnySubtype p #[t]

/-- Whether `p` may play `o` as a land from their graveyard (CR 305.9). Excludes flashback. -/
def mayPlayLandFromGraveyard (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.zone == .graveyard p && o.owner == p && isDiscardableCard o &&
    g.isLand o && g.controlsPlayLandsFromGraveyard p

/-- Whether `p` may play `o` as a land from the top of their library (CR 305.9).
Excludes cast-only creature permissions such as Elven Chorus. -/
def mayPlayLandFromLibraryTop (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.zone == .library p &&
    (g.player p).library.back? == some o.id &&
    g.isLand o && g.controlsPlayLandsFromTop p

/-- Whether `p` may play `o` as a land from its current zone (CR 305.9), excluding
cast-only permissions (Elven Chorus creature-only library top, flashback,
`mayCastExiledBySource`, and exile permissions that only allow casting such as
`withoutManaCost`, `payLifeEqualManaValue`, `prepareSource`, or `fromAdventure`). -/
def mayPlayLand (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  isDiscardableCard o && g.isLand o &&
    ((g.player p).hand.contains o.id || g.mayPlayLandFromExile p o ||
      g.mayPlayLandFromGraveyard p o || g.mayPlayLandFromLibraryTop p o)

def mayPlay (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  isCastableObject o &&
    ((g.player p).hand.contains o.id || g.mayPlayFromExile p o || g.mayCastExiledBySource p o ||
      g.mayPlayFromGraveyard p o || g.mayPlayFromLibraryTop p o)

def playZoneError (g : Game) (p : PlayerId) (o : GameObject) : String :=
  if o.zone == .exile && !g.mayPlayFromExile p o && !g.mayCastExiledBySource p o then
    "You may not play that card from exile"
  else if o.zone == .graveyard p && !g.mayPlayFromGraveyard p o then
    "You may not play that card from your graveyard"
  else if o.zone == .library p && !g.mayPlayFromLibraryTop p o then
    "You may not play that card from the top of your library"
  else
    "That card is not in your hand"

def playLandZoneError (g : Game) (p : PlayerId) (o : GameObject) : String :=
  if o.zone == .exile && !g.mayPlayLandFromExile p o then
    "You may not play that card from exile"
  else if o.zone == .graveyard p && !g.mayPlayLandFromGraveyard p o then
    "You may not play that card from your graveyard"
  else if o.zone == .library p && !g.mayPlayLandFromLibraryTop p o then
    "You may not play that card from the top of your library"
  else
    "That card is not in your hand"

end Game
end Mtg.Engine
