import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.PermanentAction
import Mtg.Engine.Card.Targeting
import Mtg.Engine.Card.Token
import Mtg.Engine.TypeLine

/-!
# Spell resolutions (CR 608)

How a spell resolves, the demonstration agent's spell classification, and
the Oracle wording of each shape.
-/

namespace Mtg.Engine

/-- How the demonstration agent classifies a spell when choosing what to cast.
Adding a constructor is a compile error in `SpellResolution.toPhrase` rather than
silently skipping the new effect. -/
inductive SpellCastKind where
  /-- Damage to any target (player or creature). -/
  | burn
  /-- Damage to a creature only (including Smite-style follow-ups). -/
  | creatureDamage
  /-- A creature you control deals its power to an opposing creature. -/
  | fight
  /-- Destroy target creature with flying. -/
  | destroyFlying
  /-- Destroy target creature. -/
  | destroyCreature
  /-- Destroy target artifact or land. -/
  | destroyArtifactOrLand
  /-- Until-end-of-turn pump or +1/+1 with keyword grants. -/
  | pump
  /-- You may play an additional land this turn. -/
  | extraLand
  /-- Mass until-end-of-turn P/T change. -/
  | massPump
  /-- Draw cards, optionally losing life (e.g. Night's Whisper). -/
  | draw
  /-- Counter a spell. -/
  | counter
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which creatures an until-end-of-turn pump affects. -/
inductive CreaturePumpScope where
  /-- Every creature. -/
  | all
  /-- Creatures the targeted player controls. -/
  | ofTargetPlayer
  /-- Creatures the controller of the resolving spell controls. -/
  | youControl
deriving Repr, Inhabited, BEq, DecidableEq

/-- Who gains the life from `SpellResolution.gainLife`. -/
inductive LifeGainer where
  /-- The controller of the resolving spell or ability. -/
  | you
  /-- Each announced player target. -/
  | targetPlayers
deriving Repr, Inhabited, BEq, DecidableEq

/-- Who draws the cards from `SpellResolution.draw`. -/
inductive CardDrawer where
  /-- The controller of the resolving spell or ability. -/
  | you
  /-- The announced player target. -/
  | targetPlayer
deriving Repr, Inhabited, BEq, DecidableEq

/-- Who loses the life from `SpellResolution.loseLife`. -/
inductive LifeLoser where
  /-- The controller of the resolving spell or ability. -/
  | you
  /-- The announced player target. -/
  | targetPlayer
  /-- The controller of the targeted permanent. -/
  | controllerOfTarget
  /-- Each opponent of the controller. -/
  | eachOpponent
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which milled cards `SpellResolution.millThenPut` puts into hand. -/
inductive MilledToHand where
  /-- Up to one card of type `a` or `b`. A lone eligible card is taken. -/
  | oneOf (a b : CardType)
  /-- Up to `max` cards of type `ty`. The player may take fewer. -/
  | upTo (max : Nat) (ty : CardType)
  /-- Every milled card of type `a` or `b`. -/
  | allOf (a b : CardType)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which spells `SpellResolution.spellsCostLessThisTurn` makes cheaper. -/
inductive SpellCostLess where
  /-- Spells of this card type (CR 205.2a). -/
  | cardType (ty : CardType)
  /-- Spells of this supertype (CR 205.4a). -/
  | supertype (s : Supertype)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which creatures `SpellResolution.dealDamageToEachCreature` damages. -/
inductive EachCreatureDamage where
  /-- Every creature. -/
  | each
  /-- Each creature an opponent of the controller controls. -/
  | opponentsControl
  /-- Each creature that does not have this subtype. -/
  | nonSubtype (subtype : String)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Who creates the tokens from `SpellResolution.createTokens`. -/
inductive TokenCreator where
  /-- The controller of the resolving spell or ability. -/
  | you
  /-- The announced player target. -/
  | targetPlayer
deriving Repr, Inhabited, BEq, DecidableEq

/-- How many tokens `SpellResolution.createTokens` creates. -/
inductive TokenQuantity where
  /-- The `n` argument. -/
  | fixed
  /-- X, chosen as the spell was cast. -/
  | chosenX
  /-- One token for each permanent of this subtype the creator controls. -/
  | perSubtype (subtype : String)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Where the damage from `SpellResolution.dealDamageToEachCreature` comes from. -/
inductive EachCreatureAmount where
  /-- The `n` argument. -/
  | fixed
  /-- The total mana value of other spells the controller has cast this turn.
  The resolving spell itself is not counted. -/
  | otherSpellsManaValue
deriving Repr, Inhabited, BEq, DecidableEq

/-- How `SpellResolution.mutualFight` uses the announced creatures. -/
inductive MutualFight where
  /-- Both announced creatures must still be legal. Each deals damage equal
  to its power to the other. -/
  | both
  /-- The creature you control fights up to one other creature. No second
  target means it has nothing to fight. -/
  | upToOne
deriving Repr, Inhabited, BEq, DecidableEq

/-- How `SpellResolution.searchLibrary` searches. -/
inductive LibrarySearch where
  /-- The controller searches their library and puts the card into their hand. -/
  | youToHand
  /-- The targeted permanent's owner may search and put the card onto the
  battlefield tapped. -/
  | ownerMayToBattlefield
deriving Repr, Inhabited, BEq, DecidableEq

/-- When `SpellResolution.if` and `SpellResolution.ifElse` choose a branch. -/
inductive SpellIf where
  /-- The targeted permanent has this subtype. -/
  | subtype (subtype : String)
  /-- The targeted spell's mana value was this much or less.
  That value includes `{X}` from when the spell was on the stack (CR 202.3e). -/
  | mvAtMost (n : Nat)
  /-- The resolving spell was cast from a graveyard. -/
  | castFromGraveyard
  /-- The resolving spell was cast using teamwork. -/
  | teamwork
  /-- A gift was promised as the spell was cast. -/
  | giftPromised
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which announced creatures `SpellResolution.countersOnCreatureTargets`
puts counters on. -/
inductive CreatureCounterTargets where
  /-- Each announced target that is still a legal creature. A player target
  is left alone. -/
  | each
  /-- The first announced target, when it is a creature the controller of the
  resolving spell controls. -/
  | firstYouControl
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which creatures you control `SpellResolution.plusOneOnEachYouControl` affects. -/
inductive YouControlCounters where
  /-- Each creature you control. -/
  | each
  /-- Each creature you control other than the first announced target. -/
  | eachOther
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which targeted card `SpellResolution.returnTargetToHand` returns to a hand. -/
inductive ReturnedCard where
  /-- A spell on the stack, returned to its owner's hand. -/
  | spell
  /-- A graveyard card. Up to one, returned to your hand. -/
  | graveyard
deriving Repr, Inhabited, BEq, DecidableEq

/-- The event `SpellResolution.replace` replaces. -/
inductive ReplaceEvent where
  /-- The targeted permanent dying this turn. -/
  | diesThisTurn
deriving Repr, Inhabited, BEq, DecidableEq

/-- What `SpellResolution.replace` does instead of `ReplaceEvent`. -/
inductive ReplaceInstead where
  /-- Exile it. -/
  | exile
deriving Repr, Inhabited, BEq, DecidableEq

/-- How a spell resolves (CR 608). Grouped so `Game.applyEffect` matches a
handful of shapes instead of every printed spell factory. Burn and
creature-only damage both use `onPermanent (.dealDamage n)`; Game applies
that action to a player or a creature when the targeting shape allows it. -/
inductive SpellResolution where
  /-- You may play an additional land this turn. -/
  | extraLand
  /-- A creature you control deals `k` times its power to an opposing creature.
  One times its power is `.fight` (the default). Twice its power is `.fight 2`. -/
  | fight (k : Nat := 1)
  /-- The two announced creatures fight (CR 701.12): each deals damage equal
  to its power to the other. Both creatures required is `.mutualFight` (`.both`).
  Up to one other creature is `.mutualFight .upToOne`. Counters and then the
  required fight are
  `.sequence [.countersOnCreatureTargets .plusOnePlusOne n .firstYouControl, .mutualFight]`. -/
  | mutualFight (how : MutualFight := .both)
  /-- Affect a still-legal target. Damage can hit a player or a creature;
  other actions require a permanent. -/
  | onPermanent (action : PermanentAction)
  /-- Creatures in `scope` get +P/+T until end of turn.
  Creatures you control are `.creaturesPump p t` (`.youControl`).
  Every creature is `.creaturesPump p t .all`. Creatures the targeted
  player controls are `.creaturesPump p t .ofTargetPlayer`. -/
  | creaturesPump (power toughness : Int) (scope : CreaturePumpScope := .youControl)
  /-- Exile cards of type `ty` from the targeted player's graveyard and grant
  permission to cast them, spending mana as though it were any type. -/
  | exileGraveyardCreaturesGrantCast (ty : CardType := .creature)
  /-- `who` draws `n` cards. The controller is `.draw n` (`.you`).
  The announced player target is `.draw n .targetPlayer`. -/
  | draw (n : Nat) (who : CardDrawer := .you)
  /-- Discard `n` cards. -/
  | discard (n : Nat)
  /-- `who` loses `n` life. Loss of life is not damage (CR 118.3a / 120.3).
  The controller is `.loseLife n` (`.you`).
  The announced player target is `.loseLife n .targetPlayer`.
  The targeted permanent's controller is `.loseLife n .controllerOfTarget`.
  Each opponent is `.loseLife n .eachOpponent`. -/
  | loseLife (n : Nat) (who : LifeLoser := .you)
  /-- `who` gains `n` life. The controller is `.gainLife n` (`.you`).
  Each announced player target is `.gainLife n .targetPlayers`. -/
  | gainLife (n : Nat) (who : LifeGainer := .you)
  /-- Scry `n`. -/
  | scry (n : Nat)
  /-- Tap each targeted creature (one or two). -/
  | tapTargets
  /-- Counter the targeted spell. -/
  | counter
  /-- Resolve `r` unless its controller pays `{n}`.
  Countering unless they pay is `.unlessPays .counter n`. -/
  | unlessPays (r : SpellResolution) (n : Nat)
  /-- Counter; exile a permanent spell and grant a free cast. -/
  | counterExilePermanentMayCast
  /-- The player chooses one of these resolutions.
  Putting the target on the top or bottom of its owner's library is
  `.or [.onPermanent .putOnTopOfLibrary, .onPermanent .putOnBottomOfLibrary]`. -/
  | or (rs : List SpellResolution)
  /-- The controller may resolve `r`. Declining skips it.
  Attaching an Equipment you control is `.may .attachEquipment`. -/
  | may (r : SpellResolution)
  /-- Attach an Equipment you control to the targeted creature. -/
  | attachEquipment
  /-- Resolve `r` when `cond` holds.
  Attaching Equipment to a Dwarf is `.«if» (.may .attachEquipment) (.subtype "Dwarf")`.
  Recruiting when the targeted spell's mana value was `n` or less is
  `.«if» .recruit (.mvAtMost n)`.
  Counters on each other creature, when cast from a graveyard, are
  `.«if» (.plusOneOnEachYouControl n .eachOther) .castFromGraveyard`. -/
  | «if» (r : SpellResolution) (cond : SpellIf)
  /-- Resolve `whenTrue` when `cond` holds, and `whenFalse` otherwise.
  Drawing two cards when cast from a graveyard, and one otherwise, is
  `.ifElse (.draw 2) (.draw 1) .castFromGraveyard`.
  Amassing Goblins 3 when cast from a graveyard, and Goblins 1 otherwise, is
  `.ifElse (.amassGoblins 3) (.amassGoblins 1) .castFromGraveyard`. -/
  | ifElse (whenTrue whenFalse : SpellResolution) (cond : SpellIf)
  /-- Exchange control of the two targeted permanents. -/
  | exchangeControl
  /-- Put `n` counters of `kind` on creatures among the announced targets.
  Each legal creature target is `.countersOnCreatureTargets` (`.each`).
  The first targeted creature you control is
  `.countersOnCreatureTargets .plusOnePlusOne n .firstYouControl`. -/
  | countersOnCreatureTargets (kind : CounterKind := .plusOnePlusOne) (n : Nat := 1)
      (which : CreatureCounterTargets := .each)
  /-- Return the targeted `card` to a hand.
  A spell on the stack is `.returnTargetToHand` (`.spell`), to its owner's hand.
  A graveyard card is `.returnTargetToHand .graveyard`: up to one, to your hand. -/
  | returnTargetToHand (card : ReturnedCard := .spell)
  /-- Creatures you control gain these keywords until end of turn. -/
  | teamGain (k : Keywords)
  /-- Amass `subtype` `n`. -/
  | amassGoblins (n : Nat) (subtype : String := "Goblin")
  /-- Recruit. -/
  | recruit
  /-- Search a library for a `s` `ty` card, as `how` says.
  The controller, into their hand, is `.searchLibrary` (`.youToHand`).
  The targeted permanent's owner, who may put it onto the battlefield tapped,
  is `.searchLibrary .basic .land .ownerMayToBattlefield`. -/
  | searchLibrary (s : Supertype := .legendary) (ty : CardType := .creature)
      (how : LibrarySearch := .youToHand)
  /-- If `what` would happen, `instead` happens in its place.
  The targeted creature dying this turn, exiled instead, is
  `.replace .diesThisTurn .exile`. A pump and that replacement are
  `.sequence [.onPermanent (.pump p t), .replace .diesThisTurn .exile]`.
  Damage, losing indestructible, and that replacement are
  `.sequence [.onPermanent (.dealDamage n), .onPermanent .loseIndestructible, .replace .diesThisTurn .exile]`. -/
  | replace (what : ReplaceEvent) (instead : ReplaceInstead)
  /-- Add {R} for each permanent of type `ty` opponents control. -/
  | addRedPerOppArtifacts (ty : CardType := .artifact)
  /-- Choose a creature type and bounce the rest. -/
  | chooseTypeReturnOthers
  /-- Draw equal to greatest toughness, then put creatures onto the battlefield. -/
  | drawEqualToughnessThenPutCreatures
  /-- Mill `n`, then put cards from among them into your hand as `which` says.
  Up to one instant or sorcery is `.millThenPut n (.oneOf .instant .sorcery)`.
  Up to `max` lands is `.millThenPut n (.upTo max .land)`.
  Every instant or sorcery is `.millThenPut n (.allOf .instant .sorcery)`. -/
  | millThenPut (n : Nat) (which : MilledToHand)
  /-- Exile targeted permanents you control, then return them. -/
  | exileThenReturnYouControl
  /-- Add `n` mana in any combination of colors, spendable only on `subtype` spells. -/
  | addFourManaDragonSpells (n : Nat := 4) (subtype : String := "Dragon")
  /-- Exile attacking creatures; that player may search basics. -/
  | exileAttackersSearchBasics
  /-- Exile the top `n`; play them if you control this subtype. -/
  | exileTopPlayIfYouControlSubtype (n : Nat) (subtype : String)
  /-- Players can't cast spells this turn. A promised gift gates this with
  `.«if» .playersCantCastThisTurn .giftPromised`. -/
  | playersCantCastThisTurn
  /-- Exile the top X of the targeted opponent; play them for life. -/
  | exileTopXOppPlayForLife
  /-- Separate the top `n` cards into two piles (Riddles in the Dark). -/
  | riddlesInTheDark (n : Nat := 4)
  /-- Return this-turn battlefield-to-gy creatures as Food. -/
  | supperForSpiders
  /-- Bounce owned creatures; delayed Bird Soldiers. -/
  | eaglesAreComing
  /-- Look at the top `n`; put lands onto the battlefield tapped; gain life. -/
  | lookAtTopLandsGainLife (n life : Nat)
  /-- Gain control of targeted opposing artifacts. -/
  | gainControlOppArtifacts
  /-- Phase out the target, or each of a player's creatures if kicked. -/
  | phaseOutKicker
  /-- Deal `n` damage to the targeted permanent's controller.
  Teamwork gates this with `.«if» (.dealDamageToControllerOfTarget n) .teamwork`. -/
  | dealDamageToControllerOfTarget (n : Nat)
  /-- Exile MV-limited creature, or any plus gain life if teamwork. -/
  | exileCreatureMvAtMostOrAnyIfTeamwork (n life : Nat)
  /-- Return a gy creature, MV-limited unless teamwork. -/
  | returnGyCreatureMvAtMostOrAny (n : Nat)
  /-- Reveal the top `n` and put creatures onto the battlefield. -/
  | revealTopPutCreatures (n : Nat)
  /-- `who` creates tokens of `kind`. `n` is the count when `qty` is `.fixed`.
  The controller creates `n` with `.createTokens kind n` (`.you` `.fixed`).
  The announced player target is `.createTokens kind n .targetPlayer`.
  X tokens are `.createTokens kind 0 (qty := .chosenX)`.
  One for each of `subtype` you control is
  `.createTokens kind 0 (qty := .perSubtype subtype)`. -/
  | createTokens (kind : TokenKind) (n : Nat) (who : TokenCreator := .you)
      (qty : TokenQuantity := .fixed)
  /-- Return one or two targeted nonlands to hand. -/
  | returnOneOrTwoNonlands
  /-- Surveil `n` (CR 701.25). -/
  | surveil (n : Nat)
  /-- The targeted player investigates. -/
  | targetPlayerInvestigates
  /-- Apply `action` to the creature among the announced targets. -/
  | onCreatureAmongTargets (action : PermanentAction)
  /-- Deal damage to each creature in `which`. `n` is the amount when `amount`
  is `.fixed` (the default). Every creature is `.dealDamageToEachCreature n`
  (`.each`). Creatures opponents control are
  `.dealDamageToEachCreature n .opponentsControl`. Creatures that are not
  `subtype` are `.dealDamageToEachCreature n (.nonSubtype subtype)`.
  Damage equal to other spells' mana value, to creatures opponents control, is
  `.dealDamageToEachCreature 0 .opponentsControl .otherSpellsManaValue`. -/
  | dealDamageToEachCreature (n : Nat) (which : EachCreatureDamage := .each)
      (amount : EachCreatureAmount := .fixed)
  /-- Return a graveyard card of this subtype to hand. -/
  | returnGySubtypeToHand (subtype : String)
  /-- Become a P/T artifact creature and gain `kw`. -/
  | becomeArtifactCreature44Flying (p : Int := 4) (t : Int := 4) (kw : String := "flying")
  /-- Discard `n` cards unless a card of type `ty` is discarded. -/
  | discardTwoUnlessArtifact (n : Nat := 2) (ty : CardType := .artifact)
  /-- `n` +1/+1 counters on creatures you control.
  Each creature is `.plusOneOnEachYouControl` (`.each`).
  Each creature other than the first announced target is
  `.plusOneOnEachYouControl n .eachOther`. -/
  | plusOneOnEachYouControl (n : Nat := 1) (which : YouControlCounters := .each)
  /-- `n` +1/+1 counters on a creature you control. -/
  | plusOneOnCreatureN (n : Nat)
  /-- Exile the top `n` cards. You may play them until your next turn. -/
  | exileTopPlayUntilNext (n : Nat)
  /-- Destroy up to one nonland. -/
  | destroyUpToOneNonland
  /-- Create Galactus. -/
  | createGalactus
  /-- Worlds Within Worlds. -/
  | worldsWithinWorlds
  /-- Exile hand, draw, play exiled cards. -/
  | exileHandDrawPlayUntilNext
  /-- Copy nontoken creatures you control. -/
  | copyNontokenCreaturesYouControl
  /-- Gain control until EOT or next turn if a bigger Villain. -/
  | gainControlUntilEotOrNextIfVillain
  /-- Mill, maybe take a permanent, gain life. -/
  | millThenPutPermanentGainLife (n life : Nat)
  /-- Search library or graveyard for an artifact creature. -/
  | searchLibraryOrGyArtifactCreatureX
  /-- Gain life, search a basic, +1/+1 on up to one. -/
  | gainLifeSearchBasicPlusOne (life : Nat)
  /-- Next red or green creature is free. -/
  | nextFreeRGCreature
  /-- Owner puts the creature into their library; you may connive. -/
  | ownerPutsLibraryThenConnive
  /-- Copy this spell X times, then deal damage. -/
  | copyThisSpellXTimesThenDamage (n : Nat)
  /-- Maybe draw one card for each permanent of type `ty`; opponents draw if you do. -/
  | mayDrawPerArtifactOppsDraw (ty : CardType := .artifact)
  /-- Maybe put a `subtype` creature from hand with mana value `n` or less; otherwise draw. -/
  | mayPutHeroMvOrDraw (n : Nat) (subtype : String := "Hero")
  /-- Maybe sacrifice or discard, then draw. -/
  | maySacArtifactOrDiscardDraw (cards : Nat)
  /-- Return up to two modal graveyard cards. -/
  | returnUpToTwoGyModal
  /-- Spells described by `which` cost `{n}` less this turn.
  Card type `ty` is `.spellsCostLessThisTurn (.cardType ty) n`.
  Supertype `s` is `.spellsCostLessThisTurn (.supertype s) n`. -/
  | spellsCostLessThisTurn (which : SpellCostLess) (n : Nat)
  /-- Apply each resolution in order. -/
  | sequence (rs : List SpellResolution)
  /-- A resolution that is not a spell shape. It does not play an extra land. -/
  | unrecognized
deriving Repr, Inhabited, BEq


namespace SpellResolution

/-- The “if …” clause for `cond`, without a following resolution. -/
private def ifClause (cond : SpellIf) (noun : String) : String :=
  match cond with
  | .subtype subtype => s!"if {noun} is {indefinite subtype} {subtype}"
  | .mvAtMost n => s!"if that spell's mana value was {n} or less"
  | .castFromGraveyard => "if this spell was cast from a graveyard"
  | .teamwork => "if this spell was cast using teamwork"
  | .giftPromised => "if the gift was promised"

/-- The “if … would …” clause for `what`, without the replacement. -/
private def replaceWhatClause (what : ReplaceEvent) (noun : String) : String :=
  match what with
  | .diesThisTurn => s!"if {noun} would die this turn"

/-- What happens instead of `what`. -/
private def replaceInsteadClause (instead : ReplaceInstead) : String :=
  match instead with
  | .exile => "exile it instead"

/-- Drop one trailing period so a following clause can continue the sentence. -/
private def trimPeriod (s : String) : String :=
  if s.endsWith "." then (s.dropEnd 1).toString else s

/-- One step, not a sequence or a choice. Sequence and `or` phrasing stay
outside this match so the constructor splitter is not recursive. -/
private def phraseOne (r : SpellResolution) (noun : String) : String :=
  match r with
  | .fight 1 =>
    "target creature you control deals damage equal to its power to target creature an opponent controls"
  | .fight k =>
    s!"Target creature you control deals damage equal to {timesPhrase k} its power to target creature an opponent controls."
  | .mutualFight .both =>
    "target creature you control fights target creature an opponent controls"
  | .mutualFight .upToOne =>
    "target creature you control fights up to one other target creature"
  | .extraLand => "you may play an additional land this turn"
  | .unrecognized => "this effect does nothing"
  | .sequence _ => ""
  | .discard n => s!"discard {cardPhrase n}"
  | .loseLife n .you => s!"lose {n} life"
  | .loseLife n .targetPlayer => s!"{noun} loses {n} life"
  | .loseLife n .controllerOfTarget => s!"its controller loses {n} life"
  | .loseLife n .eachOpponent => s!"each opponent loses {n} life"
  | .gainLife n .you => s!"you gain {n} life"
  | .gainLife n .targetPlayers => s!"Target player gains {n} life"
  | .surveil n => s!"surveil {n}"
  | .teamGain k => s!"creatures you control gain {k.joinedAnd} until end of turn"
  | .returnTargetToHand .spell => s!"return {noun} to its owner's hand"
  | .returnTargetToHand .graveyard => s!"return up to one {noun} to your hand"
  | .onPermanent action => PermanentAction.toNotation action noun
  | .creaturesPump p t .youControl =>
    s!"creatures you control get {signedStat p}/{signedStat t} until end of turn"
  | .creaturesPump p t .all =>
    s!"all creatures get {signedStat p}/{signedStat t} until end of turn"
  | .creaturesPump p t .ofTargetPlayer =>
    s!"creatures {noun} controls get {signedStat p}/{signedStat t} until end of turn"
  | .exileGraveyardCreaturesGrantCast ty =>
    s!"exile all {ty.oracleWord} cards from target player's graveyard. You may cast spells from among those cards for as long as they remain exiled, and mana of any type can be spent to cast them"
  | .draw n .you => s!"draw {cardPhrase n}"
  | .draw n .targetPlayer => s!"{noun} draws {cardPhrase n}"
  | .scry n => s!"scry {n}"
  | .tapTargets => "tap one or two target creatures"
  | .counter => s!"counter {noun}"
  | .unlessPays r n =>
    let base := phraseOne r noun
    let base := if base.endsWith "." then (base.dropEnd 1).toString else base
    if base.isEmpty then s!"unless its controller pays \{{n}}"
    else s!"{base} unless its controller pays \{{n}}"
  | .counterExilePermanentMayCast =>
    s!"counter {noun}. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled"
  | .or _ => ""
  | .attachEquipment =>
    "attach an Equipment you control to it"
  | .may r =>
    let base := phraseOne r noun
    let base := if base.endsWith "." then (base.dropEnd 1).toString else base
    let base := if base.startsWith "you " then (base.drop 4).toString else base
    if base.isEmpty then "you may" else s!"you may {base}"
  | .recruit => "recruit"
  | .«if» r cond =>
    let base := trimPeriod (phraseOne r noun)
    let cond := ifClause cond noun
    if base.isEmpty then cond else s!"{cond}, {base}"
  | .ifElse (.onPermanent (.dealDamage teamworkN)) (.onPermanent (.dealDamage n)) .teamwork =>
    s!"deals {n} damage to target attacking or blocking creature. If this spell was cast using teamwork, it deals {teamworkN} damage to that creature instead"
  | .ifElse (.unlessPays .counter teamworkN) (.unlessPays .counter n) .teamwork =>
    s!"counter target spell unless its controller pays \{{n}}. Counter that spell unless its controller pays \{{teamworkN}} instead if this spell was cast using teamwork"
  | .ifElse whenTrue whenFalse cond =>
    let no := trimPeriod (phraseOne whenFalse noun)
    let yes := trimPeriod (phraseOne whenTrue noun)
    let cond := ifClause cond noun
    if no.isEmpty then
      if yes.isEmpty then cond else s!"{cond}, {yes}"
    else if yes.isEmpty then no
    else s!"{no}. {capitalizeAscii cond}, {yes} instead"
  | .exchangeControl =>
    "exchange control of two target nonland permanents that share a card type"
  | .countersOnCreatureTargets kind n .each =>
    s!"put {kind.countersPhrase n} on up to one target creature"
  | .countersOnCreatureTargets kind n .firstYouControl =>
    s!"put {kind.countersPhrase n} on target creature you control"
  | .amassGoblins n subtype =>
    s!"amass {pluralizeName subtype} {n}"
  | .searchLibrary s ty .youToHand =>
    searchLibraryToHandPhrase s!"a {s.oracleWord} {ty.oracleWord} card"
  | .searchLibrary s ty .ownerMayToBattlefield =>
    s!"its controller may search their library for a {s.oracleWord} {ty.oracleWord} card, put it onto the battlefield tapped, then shuffle"
  | .dealDamageToEachCreature _ .opponentsControl .otherSpellsManaValue =>
    "deals damage to each creature your opponents control equal to the total mana value of other spells you've cast this turn"
  | .dealDamageToEachCreature n .each .fixed =>
    s!"deals {n} damage to each creature"
  | .dealDamageToEachCreature n .opponentsControl .fixed =>
    s!"deals {n} damage to each creature your opponents control"
  | .dealDamageToEachCreature n (.nonSubtype subtype) .fixed =>
    s!"deals {n} damage to each non-{subtype} creature"
  | .dealDamageToEachCreature _ .each .otherSpellsManaValue =>
    "deals damage to each creature equal to the total mana value of other spells you've cast this turn"
  | .dealDamageToEachCreature _ (.nonSubtype subtype) .otherSpellsManaValue =>
    s!"deals damage to each non-{subtype} creature equal to the total mana value of other spells you've cast this turn"
  | .replace what instead =>
    s!"{replaceWhatClause what noun}, {replaceInsteadClause instead}"
  | .addRedPerOppArtifacts ty =>
    s!"add {"{R}"} for each {ty.oracleWord} your opponents control"
  | .chooseTypeReturnOthers =>
    "choose a creature type. Return all creatures that aren't of the chosen type to their owners' hands"
  | .drawEqualToughnessThenPutCreatures =>
    "draw cards equal to the greatest toughness among creatures you control, then put any number of creature cards from your hand onto the battlefield"
  | .millThenPut n (.oneOf a b) =>
    s!"mill {n} cards, then put {indefinite a.oracleWord} {a.oracleWord} or {b.oracleWord} card from among them into your hand"
  | .millThenPut n (.upTo max ty) =>
    s!"mill {n} cards, then put up to {englishNumber max} {ty.oracleWord} cards from among them into your hand"
  | .millThenPut n (.allOf a b) =>
    s!"mill {n} cards, then put all {a.oracleWord} and {b.oracleWord} cards from among them into your hand"
  | .exileThenReturnYouControl =>
    "exile two target creatures and/or lands you control, then return them to the battlefield under their owner's control"
  | .addFourManaDragonSpells n subtype =>
    s!"add {englishNumber n} mana in any combination of colors. Spend this mana only to cast {subtype} spells"
  | .exileAttackersSearchBasics =>
    s!"exile all attacking creatures {noun} controls. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle"
  | .exileTopPlayIfYouControlSubtype n subtype =>
    s!"look at the top {n} cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a {subtype}"
  | .playersCantCastThisTurn =>
    "players can't cast spells this turn"
  | .exileTopXOppPlayForLife =>
    "exile the top X cards of target opponent's library. You may play those cards this turn. If you cast a spell this way, pay life equal to its mana value rather than pay its mana cost"
  | .riddlesInTheDark n =>
    s!"look at the top {englishNumber n} cards of your library and separate them into a face-down pile and a face-up pile. An opponent chooses one of the piles. Put that pile into your hand and the other into your graveyard"
  | .supperForSpiders =>
    "put onto the battlefield under your control all creature cards in your opponents' graveyards that were put there from the battlefield this turn. They are Food artifacts with \"{2}, {T}, Sacrifice this artifact: You gain 3 life.\""
  | .eaglesAreComing =>
    "choose target creature you own. If this spell was kicked, instead choose any number of target creatures you own. Return each chosen creature to your hand. At the beginning of the next upkeep, create a 4/4 white Bird Soldier creature token with flying for each creature returned to your hand this way"
  | .lookAtTopLandsGainLife n life =>
    s!"look at the top {n} cards of your library, put any number of land cards from among them onto the battlefield tapped, then shuffle. You gain {life} life"
  | .gainControlOppArtifacts =>
    "for each opponent, gain control of up to one target artifact that player controls"
  | .phaseOutKicker =>
    "target creature phases out. If this spell was kicked, each creature target player controls phases out instead"
  | .dealDamageToControllerOfTarget n =>
    s!"it also deals {n} damage to that creature's controller"
  | .exileCreatureMvAtMostOrAnyIfTeamwork n life =>
    s!"exile target creature with mana value {n} or less. If this spell was cast using teamwork, instead exile target creature and you gain {life} life"
  | .returnGyCreatureMvAtMostOrAny n =>
    s!"choose target creature card in your graveyard with mana value {n} or less. If this spell was cast using teamwork, instead choose target creature card in your graveyard. Return the chosen card to the battlefield"
  | .revealTopPutCreatures n =>
    s!"reveal the top {n} cards of your library. You may put a creature card from among them onto the battlefield. If this spell was cast using teamwork, put any number of creature cards from among them onto the battlefield instead. Put the rest into your graveyard"
  | .createTokens kind _ _ .chosenX =>
    s!"create X {kind.pluralNoun}"
  | .createTokens kind _ _ (.perSubtype subtype) =>
    s!"Create a {kind.oracleNoun} for each {subtype} you control"
  | .createTokens kind n .you .fixed =>
    TokenKind.createPhrase kind n
  | .createTokens kind n .targetPlayer .fixed =>
    s!"{noun} creates {TokenKind.createdTokensPhrase kind n}"
  | .returnOneOrTwoNonlands =>
    "return one or two target nonland permanents to their owners' hands"
  | .targetPlayerInvestigates =>
    "target player investigates"
  | .onCreatureAmongTargets action =>
    PermanentAction.toNotation action "target creature"
  | .returnGySubtypeToHand subtype =>
    s!"return target {subtype} card from your graveyard to your hand"
  | .becomeArtifactCreature44Flying p t kw =>
    s!"until end of turn, {noun} becomes an artifact creature with base power and toughness {p}/{t} and gains {kw}"
  | .discardTwoUnlessArtifact n ty =>
    s!"discard {englishNumber n} cards unless you discard {indefinite ty.oracleWord} {ty.oracleWord} card"
  | .plusOneOnEachYouControl n .each =>
    s!"put {plusOnePlusOneCountersPhrase n} on each creature you control"
  | .plusOneOnEachYouControl n .eachOther =>
    s!"put {plusOnePlusOneCountersPhrase n} on each other creature you control"
  | .plusOneOnCreatureN n =>
    s!"put {plusOnePlusOneCountersPhrase n} on {noun}"
  | .exileTopPlayUntilNext _ =>
    s!"exile the top card of your library. {playThatCardUntilNextTurnPhrase}"
  | .destroyUpToOneNonland =>
    "Destroy up to one target nonland permanent"
  | .createGalactus =>
    "Create Galactus, a legendary 16/16 black Elder Alien creature token with flying, trample, and \"Whenever Galactus attacks, destroy target land.\""
  | .worldsWithinWorlds =>
    "Exile all creatures. Each player may put any number of creature cards from their hand onto the battlefield. Then put all cards exiled this way into their owners' hands. Exile Worlds Within Worlds."
  | .exileHandDrawPlayUntilNext =>
    "Exile all the cards from your hand, then draw that many cards. Until the end of your next turn, you may play cards exiled this way."
  | .copyNontokenCreaturesYouControl =>
    "For each nontoken creature you control, create a token that's a copy of that creature, except it isn't legendary."
  | .gainControlUntilEotOrNextIfVillain =>
    "Gain control of target creature until end of turn. If you control a Villain with greater mana value than that creature, gain control of that creature until the end of your next turn instead. Untap that creature. It gains haste until end of turn."
  | .millThenPutPermanentGainLife n life =>
    s!"Mill {n} cards. You may put a permanent card from among the milled cards into your hand. You gain {life} life."
  | .searchLibraryOrGyArtifactCreatureX =>
    "Search your library and/or graveyard for an artifact creature card with mana value X or less and put it onto the battlefield with X additional +1/+1 counters on it. If X is 4 or greater, it gains haste until end of turn. If you search your library this way, shuffle."
  | .gainLifeSearchBasicPlusOne life =>
    s!"Target player gains {life} life, then searches their library for a basic land card, puts it onto the battlefield tapped, then shuffles. Put a +1/+1 counter on up to one target creature."
  | .nextFreeRGCreature =>
    "The next red or green creature spell you cast this turn can be cast without paying its mana cost"
  | .ownerPutsLibraryThenConnive =>
    "The owner of target creature an opponent controls puts it into their library second from the top or on the bottom. Then up to one target creature you control connives."
  | .copyThisSpellXTimesThenDamage n =>
    s!"When you cast this spell, copy it X times. You may choose new targets for the copies.\ndeals {n} damage to target creature."
  | .mayDrawPerArtifactOppsDraw ty =>
    s!"You may draw a card for each {ty.oracleWord} you control. If you do, each opponent draws a card"
  | .mayPutHeroMvOrDraw n subtype =>
    s!"You may put {indefinite subtype} {subtype} creature card with mana value {n} or less from your hand onto the battlefield. If you don't, draw a card"
  | .maySacArtifactOrDiscardDraw cards =>
    s!"You may sacrifice an artifact or discard a card. If you do, draw {cardPhrase cards}."
  | .returnUpToTwoGyModal =>
    "Choose up to two. Return those cards from your graveyard to your hand. • Target artifact card. • Target creature card. • Target enchantment card. • Target land card."
  | .spellsCostLessThisTurn (.cardType ty) n =>
    s!"{ty} spells you cast this turn cost \{{n}} less to cast"
  | .spellsCostLessThisTurn (.supertype s) n =>
    s!"{s} spells you cast this turn cost \{{n}} less to cast"

/-- Nested `sequence` constructors, left to right. An `or` stays one step:
flattening it would resolve every alternative. -/
def flatten : SpellResolution → List SpellResolution
  | .sequence rs => rs.flatMap flatten
  | r => [r]

/-- Printed wording of a flat sequence. Known shapes keep their Oracle text;
other sequences join each step. -/
private def phraseSequence (rs : List SpellResolution) (noun : String) : String :=
  match rs with
  | [.draw n .you, .discard 1] =>
    s!"draw {cardPhrase n}, then discard a card"
  | [.draw cards .you, .loseLife life .you] =>
    s!"you draw {cardPhrase cards} and lose {life} life"
  | [.draw cards .targetPlayer, .loseLife life .targetPlayer] =>
    s!"{noun} draws {cardPhrase cards} and loses {life} life"
  | [.onPermanent .destroy, .loseLife n .controllerOfTarget] =>
    s!"destroy {noun}. Its controller loses {n} life"
  | [.returnTargetToHand .spell, .draw 1 .you] =>
    s!"return {noun} to its owner's hand. Draw a card"
  | [.counter, .«if» .recruit (.mvAtMost n)] =>
    s!"counter {noun}. If that spell's mana value was {n} or less, recruit"
  | [.returnTargetToHand .graveyard, .amassGoblins n subtype] =>
    s!"return up to one {noun} to your hand. Amass {pluralizeName subtype} {n}"
  | [.draw 1 .you, .loseLife 1 .you, .amassGoblins n subtype] =>
    s!"you draw a card and lose 1 life. Amass {pluralizeName subtype} {n}"
  | [.createTokens kind n .you .fixed, .creaturesPump p t .youControl] =>
    let tokens := capitalizeAscii (TokenKind.createPhrase kind n)
    s!"{tokens}, then creatures you control get {signedStat p}/{signedStat t} until end of turn."
  | [.onPermanent .destroy, .gainLife n .you] =>
    s!"destroy {noun}. You gain {n} life"
  | [.onPermanent .destroy, .surveil 1] =>
    s!"destroy {noun}. Surveil 1"
  | [.onPermanent .tap, .scry scryN, .draw drawN .you] =>
    s!"tap {noun}. Scry {scryN}. Draw {cardPhrase drawN}"
  | [.onPermanent (.pump p t), .draw 1 .you] =>
    let tStr := if t == 0 && p < 0 then "-0" else signedStat t
    s!"Target creature gets {signedStat p}/{tStr} until end of turn.\nDraw a card."
  | [.onPermanent (.plusOne 1), .onPermanent (.grantKeywords k)] =>
    if k == Keyword.lifelink.merge Keyword.indestructible then
      "put a +1/+1 counter on target creature. It gains lifelink and indestructible until end of turn"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | [.onPermanent (.grantKeywords k), .draw 1 .you] =>
    if k == Keyword.vigilance.merge Keyword.cantBeBlocked then
      s!"{noun} gains vigilance until end of turn and can't be blocked this turn"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | [.creaturesPump p t .youControl, .teamGain k] =>
    s!"Creatures you control get {signedStat p}/{signedStat t} and gain {k.joinedAnd} until end of turn"
  | [.onPermanent .untap, .onPermanent (.pump p t), .«if» (.may .attachEquipment) (.subtype subtype)] =>
    s!"untap {noun}. It gets {signedStat p}/{signedStat t} until end of turn. If it's {indefinite subtype} {subtype}, you may attach an Equipment you control to it"
  | [.countersOnCreatureTargets kind k .firstYouControl, .mutualFight .both] =>
    s!"put {kind.countersPhrase k} on target creature you control. Then it fights target creature an opponent controls"
  | [.countersOnCreatureTargets kind k .firstYouControl,
     .«if» (.plusOneOnEachYouControl m .eachOther) .castFromGraveyard] =>
    s!"put {kind.countersPhrase k} on target creature you control. If this spell was cast from a graveyard, also put {plusOnePlusOneCountersPhrase m} on each other creature you control"
  | [.dealDamageToEachCreature n (.nonSubtype sub) .fixed, .addFourManaDragonSpells m sub2] =>
    s!"deals {n} damage to each non-{sub} creature. Add {englishNumber m} mana in any combination of colors. Spend this mana only to cast {sub2} spells"
  | [.returnTargetToHand .spell, .«if» .playersCantCastThisTurn .giftPromised] =>
    "return target spell to its owner's hand. If the gift was promised, players can't cast spells this turn"
  | [.onPermanent (.dealDamage n), .«if» (.dealDamageToControllerOfTarget extra) .teamwork] =>
    s!"deals {n} damage to target creature. If this spell was cast using teamwork, it also deals {extra} damage to that creature's controller"
  | [.onPermanent (.grantKeywords k), .«if» (.onPermanent (.grantKeywords kw)) .teamwork] =>
    if k == Keyword.doubleStrike then
      s!"target creature gains double strike until end of turn. If this spell was cast using teamwork, that creature also gains {kw.joinedAnd} until end of turn"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | [.targetPlayerInvestigates,
     .onCreatureAmongTargets (.grantKeywords k),
     .onCreatureAmongTargets .untap,
     .onCreatureAmongTargets (.pump 1 0)] =>
    if k == Keyword.flying then
      "target player investigates. Target creature gets +1/+0 and gains flying until end of turn. Untap it"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | [.countersOnCreatureTargets kind k .each, .gainLife n .targetPlayers] =>
    s!"put {kind.countersPhrase k} on up to one target creature. Target player gains {n} life"
  | [.onPermanent .destroy, .searchLibrary s ty .ownerMayToBattlefield] =>
    s!"destroy {noun}. Its controller may search their library for a {s.oracleWord} {ty.oracleWord} card, put it onto the battlefield tapped, then shuffle"
  | [.draw 3 .you, .discardTwoUnlessArtifact n ty] =>
    s!"draw three cards. Then discard {englishNumber n} cards unless you discard {indefinite ty.oracleWord} {ty.oracleWord} card"
  | [.replace .diesThisTurn .exile, .onPermanent (.dealDamage n)] =>
    s!"deals {n} damage to {noun}. If that creature would die this turn, exile it instead"
  | [.onPermanent (.pump p t), .replace .diesThisTurn .exile] =>
    s!"{noun} gets {signedStat p}/{signedStat t} until end of turn. If that creature would die this turn, exile it instead"
  | [.onPermanent (.dealDamage n), .onPermanent .loseIndestructible, .replace .diesThisTurn .exile] =>
    s!"deals {n} damage to {noun}. That creature loses indestructible until end of turn. If that creature would die this turn, exile it instead"
  | [.onPermanent (.pump p t), .exileTopPlayUntilNext 1] =>
    s!"Target creature gets {signedStat p}/{signedStat t} until end of turn.\nExile the top card of your library. {playThatCardUntilNextTurnPhrase}."
  | [.onPermanent .doublePowerAndToughness, .onPermanent (.grantKeywords k)] =>
    if k == Keyword.trample then
      "Choose target creature you control. Until end of turn, double its power and toughness and it gains trample"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | _ =>
    String.intercalate ". " (rs.map (phraseOne · noun))

/-- Printed wording of a choice. The library pair keeps its Oracle sentence;
other choices join each alternative. -/
private def phraseOr (rs : List SpellResolution) (noun : String) : String :=
  match rs with
  | [.onPermanent .putOnTopOfLibrary, .onPermanent .putOnBottomOfLibrary] =>
    s!"{noun}'s owner puts it on their choice of the top or bottom of their library"
  | [.onPermanent .putOnBottomOfLibrary, .onPermanent .putOnTopOfLibrary] =>
    s!"{noun}'s owner puts it on their choice of the top or bottom of their library"
  | _ =>
    String.intercalate " or " ((rs.map (phraseOne · noun)).filter (· != ""))

/-- Oracle-style reminder from targeting and resolution. `.fight` is the
one-sided Quarrel wording, including a multiple of that power. `.mutualFight`
is the two-creature fight, including the later step of a counter-then-fight
sequence and a fight of up to one other creature. -/
def toPhrase (r : SpellResolution) (noun : String) : String :=
  match r with
  | .sequence rs => phraseSequence (rs.flatMap flatten) noun
  | .or rs => phraseOr rs noun
  | r => phraseOne r noun

end SpellResolution

end Mtg.Engine
