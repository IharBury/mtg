import Mtg.Engine.Game.StateBasedActions

/-!
# Priority and play timing (CR 117 / 116.2a)

Multiplayer flags, who has priority, sorcery-speed checks, land-play
allowances (CR 305.2b), and permission to play cards from exile, the
graveyard, or the top of the library (CR 118.12 / 400.7).
-/

namespace Mtg.Engine
namespace Game

/-- CR 100.1b: a multiplayer game begins with more than two players. -/
def isMultiplayer (g : Game) : Bool :=
  g.players.size > 2

/-- CR 103.8a: in a two-player game the starting player skips the draw step
of their first turn. Multiplayer games do not skip that draw (CR 103.8c). -/
def skipsFirstDraw (g : Game) : Bool :=
  g.isFirstTurn && !g.isMultiplayer && g.activePlayer == g.startingPlayer

/-- Whether a player currently receives priority (CR 117.3a, 502.4, 514.3,
103.8a / 500.11). A skipped draw step grants none. -/
def playersReceivePriority (g : Game) : Bool :=
  if g.step == .cleanup then g.cleanupGivesPriority
  else if g.step == .draw && g.skipsFirstDraw then false
  else g.step.playersReceivePriority

def asSorcery? (g : Game) (p : PlayerId) : Bool :=
  !g.over && g.pending == .none && g.stack.isEmpty &&
  g.step.isMainPhase && g.activePlayer == p && g.priority == p

def hasPriority (g : Game) (p : PlayerId) : Bool :=
  !g.over && g.pending == .none && g.priority == p && g.playersReceivePriority

/-- Extra land plays from permanents such as Thranduil's Company. Each such
permanent is cumulative with other extra-land effects (rulings 288 / 306). -/
def extraLandsFromPermanents (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).foldl (fun acc o =>
    match o.printed.extraLandIfOtherSubtype with
    | none => acc
    | some t =>
      if (g.permanentsOf p).any (fun other =>
        other.id != o.id && g.hasSubtype other t) then
        acc + 1
      else acc) 0

/-- How many lands `p` may play this turn (CR 305.2 / 305.2b). -/
def landPlaysAllowed (g : Game) (p : PlayerId) : Nat :=
  1 + (g.player p).additionalLandsThisTurn + g.extraLandsFromPermanents p

/-- Lands remaining this turn (CR 305.2 / 305.3 / 116.2a). -/
def canPlayLand (g : Game) (p : PlayerId) : Bool :=
  g.asSorcery? p && (g.player p).landsPlayedThisTurn < g.landPlaysAllowed p

/-- Whether `p` may play `o` from exile under a granted permission (CR 701.14 / 715.3d). -/
def mayPlayFromExile (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.zone == .exile &&
  match o.playPermission with
  | some perm =>
    perm.player == p &&
      (perm.fromAdventure || perm.whileExiled || perm.turnEndsRemaining > 0) &&
      (match perm.requireSubtype with
       | none => true
       | some t => g.controlsAnySubtype p #[t])
  | none => false

/-- Cards in exile that `p` currently may play. -/
def exiledPlayable (g : Game) (p : PlayerId) : Array GameObject :=
  g.objects.filter (fun o => g.mayPlayFromExile p o)

/-- Mole Man lets you play land cards from your graveyard (MSH 253 / 254).
Cycling and other activated abilities of those cards are still illegal. -/
def controlsPlayLandsFromGraveyard (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun x =>
    x.staticAbilities.any (fun
      | .mayPlayLandsFromGraveyard => true
      | _ => false))

def mayPlayFromGraveyard (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.zone == .graveyard p && o.owner == p &&
    (o.printed.flashback.isSome ||
      (o.printed.isLand && g.controlsPlayLandsFromGraveyard p))

/-- True when `p` controls a permanent that lets them look at the library top. -/
def controlsLookAtTop (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => o.printed.mayLookAtTopAnytime)

/-- True when `p` may look at the top card of their library right now.
Elven Chorus does not reveal a new top while a spell from that top is
still being cast. -/
def canLookAtLibraryTop (g : Game) (p : PlayerId) : Bool :=
  g.controlsLookAtTop p && !g.castingFromTop

/-- True when `p` controls a permanent that lets them cast creatures from
the top of their library. Does not grant flash or change timing. -/
def controlsCastCreaturesFromTop (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => o.printed.mayCastCreaturesFromTop)

/-- The top card of `p`'s library, if any. -/
def libraryTop? (g : Game) (p : PlayerId) : Option GameObject :=
  (g.player p).library.back?.bind g.findObject?

/-- True when `o` is the top card of `p`'s library and they may cast it as
a creature spell from there. Timing is still checked by `canCast`. -/
def controlsPlayLandsFromTop (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => o.printed.mayPlayLandsFromTop)

def mayPlayFromLibraryTop (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.zone == .library p &&
    (g.player p).library.back? == some o.id &&
    ((o.printed.isCreature && g.controlsCastCreaturesFromTop p) ||
      (o.printed.isLand && g.controlsPlayLandsFromTop p))

def mayPlay (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  (g.player p).hand.contains o.id || g.mayPlayFromExile p o ||
    g.mayPlayFromGraveyard p o || g.mayPlayFromLibraryTop p o

def playZoneError (g : Game) (p : PlayerId) (o : GameObject) : String :=
  if o.zone == .exile && !g.mayPlayFromExile p o then
    "You may not play that card from exile"
  else if o.zone == .graveyard p && !g.mayPlayFromGraveyard p o then
    "You may not play that card from your graveyard"
  else if o.zone == .library p && !g.mayPlayFromLibraryTop p o then
    "You may not play that card from the top of your library"
  else
    "That card is not in your hand"

end Game
end Mtg.Engine
