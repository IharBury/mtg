import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.Effect

/-!
# Spell and activated-ability effect constructors (Phase 8 unified `Instruction`)

`Effect.mkSpell` / `Effect.mkAbility` / `Effect.fraSpell` / `FraCandidates.ab`
plus the named constructors for every printed spell, activated-ability, and
Reality Fracture effect the engine models, all lowered directly onto unified
`Instruction` values (pure computed
`Effect.classifyForAgent` / `Effect.classifyAbilityForAgent`).
-/

namespace Mtg.Engine

namespace Effect

/-! ### Core Effect Builders & Reusable `ObjectExpr` Shorthands -/

private def creaturesYouControlExpr : ObjectExpr :=
  .inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])

private def allCreaturesExpr : ObjectExpr :=
  .inZones .battlefield (.hasType .creature)

private def oppCreaturesExpr : ObjectExpr :=
  .inZones .battlefield (.all #[.hasType .creature, .controlledBy .opponent])

/-- Build a spell-shaped `Effect` from targeting, Phase 8 `Instruction` body, and phrase. -/
def mkSpell (targeting : EffectTargeting) (body : Instruction)
    (phrase : String)
    (preferAsDefaultMode := false)
    (maxTargets := 0)
    (allowsZeroTargets := false) : Effect :=
  { targeting
    allowsZeroTargets
    maxTargets
    preferAsDefaultMode
    body
    phrase }

/-- Build an activated-ability `Effect` from targeting, Phase 8 `Instruction` body, and phrase. -/
def mkAbility (targeting : EffectTargeting) (body : Instruction)
    (phrase : String)
    (allowsZeroTargets := false)
    (maxTargets := 0) : Effect :=
  { targeting
    allowsZeroTargets
    maxTargets
    body
    phrase }

/-- Destroy one target of `spec`.
When `capitalize := false` (spell), phrase starts lowercase; when `true` (activated ability),
phrase starts uppercase. -/
def destroyTarget (spec : TargetSpec)
    (capitalize : Bool := false)
    (preferAsDefaultMode := false) : Effect :=
  let base := s!"destroy {spec.noun}"
  { targeting := .of spec
    preferAsDefaultMode
    body := Instruction.destroy (.target 0)
    phrase := if capitalize then capitalizeAscii base else base }

private def isCreaturePowerAtLeastSpec (spec : TargetSpec) : Bool :=
  match spec.slots.toList with
  | [{ domain := .object zs (.all #[.hasType .creature, .stat .power .ge _]), count := .exact 1, .. }] =>
    zs == .battlefield
  | _ => false

/-- The printed destroy-one-target effect for `spec`. The Oracle matcher refills a single
prototype to this so lines that differ only by the target noun stay one shape. -/
def canonicalDestroy (spec : TargetSpec) : Effect :=
  if spec == .creatureWithFlying then
    destroyTarget spec (capitalize := false) (preferAsDefaultMode := true)
  else if isCreaturePowerAtLeastSpec spec then
    destroyTarget spec (capitalize := false) (preferAsDefaultMode := true)
  else if spec == .artifact || spec == .artifactToken || spec == .noncreatureArtifact then
    destroyTarget spec (capitalize := false)
  else if spec == .colorlessNonland || spec == .artifactOrEnchantment || spec == .permanent ||
      spec == .noncreatureArtifactOrEnchantment then
    destroyTarget spec (capitalize := true)
  else
    destroyTarget spec (capitalize := false)

/-! ### Printed Spell Effect Constructors -/

def dealDamage (amount : Nat) : Effect :=
  mkSpell (.of .anyTarget)
    (Instruction.dealDamageFixed (.targetSlot 0) amount)
    s!"deals {amount} damage to any target"

def pump (power toughness : Int) : Effect :=
  mkSpell (.of .creature .own)
    (Instruction.pumpFixed (.target 0) power toughness)
    s!"target creature gets {signedStat power}/{signedStat toughness} until end of turn"

def destroyCreatureWithFlying : Effect :=
  destroyTarget .creatureWithFlying (capitalize := false) (preferAsDefaultMode := true)

def destroyCreature : Effect :=
  destroyTarget .creature (capitalize := false)

def plusOnePlusOneTrampleHexproof : Effect :=
  mkSpell (.of .creatureYouControl)
    (.seq #[
      Instruction.putPlusOne (.target 0) 1,
      Instruction.grantKeywords (.target 0) #[Keyword.trample, Keyword.hexproof]
    ])
    "put a +1/+1 counter on target creature you control. It gains trample and hexproof until end of turn"

def dealDamageToCreature (amount : Nat) : Effect :=
  mkSpell (.of .creature)
    (Instruction.dealDamageFixed (.targetSlot 0) amount)
    s!"deals {amount} damage to target creature"

/-- Deal `amount` damage. The creature loses indestructible until end of turn.
If it would die this turn, exile it instead. -/
def dealDamageLoseIndestructibleExile (amount : Nat) : Effect :=
  mkSpell (.of .creature)
    (.seq #[
      Instruction.dealDamageFixed (.targetSlot 0) amount,
      Instruction.loseKeywords (.target 0) #[Keyword.indestructible],
      Instruction.exileIfDiesThisTurn (.target 0)
    ])
    s!"deals {amount} damage to target creature. That creature loses indestructible until end of turn. If that creature would die this turn, exile it instead"

def creatureYouControlDealsPowerToOppCreature : Effect :=
  mkSpell (.of .creatureYouControlThenOppCreature)
    (.damage (.fight (.target 0) (.target 1) true))
    "target creature you control deals damage equal to its power to target creature an opponent controls"

def playAdditionalLandThisTurn : Effect :=
  mkSpell (.of .none)
    (Instruction.extraLand .you 1)
    "you may play an additional land this turn"

def destroyArtifactOrLandNonflyersCantBlock : Effect :=
  mkSpell (.of .artifactOrLand)
    (.seq #[
      Instruction.destroy (.target 0),
      .installEffect (.applyRule .untilEndOfTurn
        (.combat (.cantBlock (.matching {
          zones := .battlefield
          pred := .all #[.hasType .creature, .not (.hasKeyword .flying)]
        }) none)))
    ])
    "destroy target artifact or land. Creatures without flying can't block this turn"

def destroyTargetCreatureControllerLosesLife (life : Nat) : Effect :=
  mkSpell (.of .creature)
    (.seq #[
      Instruction.destroy (.target 0),
      Instruction.loseLifeFixed life (.controllerOf (.target 0))
    ])
    s!"destroy target creature. Its controller loses {life} life"
    (preferAsDefaultMode := true)

def allCreaturesGet (power toughness : Int) : Effect :=
  mkSpell (.of .none)
    (Instruction.pumpFixed allCreaturesExpr power toughness)
    s!"all creatures get {signedStat power}/{signedStat toughness} until end of turn"

def drawAndLoseLife (cards life : Nat) : Effect :=
  mkSpell (.of .none)
    (.seq #[Instruction.drawFixed cards, Instruction.loseLifeFixed life])
    s!"you draw {cardPhrase cards} and lose {life} life"

def targetPlayerDrawLoseLife (cards life : Nat) : Effect :=
  mkSpell (.of .player .selfPlayer)
    (.seq #[Instruction.drawFixed cards (.target 0), Instruction.loseLifeFixed life (.target 0)])
    s!"target player draws {cardPhrase cards} and loses {life} life"

def creaturesTargetPlayerGet (power toughness : Int) : Effect :=
  let targetPlayerCreatures : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .controlledBy (.ofExpr (.target 0))])
  mkSpell (.of .player)
    (Instruction.pumpFixed targetPlayerCreatures power toughness)
    s!"creatures target player controls get {signedStat power}/{signedStat toughness} until end of turn"

def pumpAndLifelink (power toughness : Int) : Effect :=
  mkSpell (.of .creature .own)
    (.seq #[
      Instruction.pumpFixed (.target 0) power toughness,
      Instruction.grantKeywords (.target 0) #[Keyword.lifelink]
    ])
    s!"target creature gets {signedStat power}/{signedStat toughness} and gains lifelink until end of turn"

/-- Until-end-of-turn +P/+T. If the creature would die this turn, exile it instead. -/
def pumpAndExileIfDies (power toughness : Int) : Effect :=
  mkSpell (.of .creature)
    (.seq #[
      Instruction.pumpFixed (.target 0) power toughness,
      Instruction.exileIfDiesThisTurn (.target 0)
    ])
    s!"target creature gets {signedStat power}/{signedStat toughness} until end of turn. If that creature would die this turn, exile it instead"
    (preferAsDefaultMode := true)

def exileGraveyardCreaturesGrantCast : Effect :=
  mkSpell (.of .player)
    (.moveZone (.inZones (.graveyardOf (.target 0)) (.hasType .creature)) .exile .exile {
      grantPlayPerm? := some {
        duration := .whileInZone .this .exile
        landsAllowed := false
        anyManaColor := true
      }
    })
    "exile all creature cards from target player's graveyard. You may cast spells from among those cards for as long as they remain exiled, and mana of any type can be spent to cast them"

def draw (n : Nat) : Effect :=
  mkSpell (.of .none)
    (Instruction.drawFixed n)
    s!"draw {cardPhrase n}"

/-- Discard `n` cards. The Oracle parser joins this with `draw` on “, then”,
so “draw N cards, then discard a card” is not its own prototype. -/
def discardCards (n : Nat) : Effect :=
  { body := Instruction.discardFixed n
    phrase := s!"discard {cardPhrase n}" }

def drawThenDiscard (n : Nat) : Effect :=
  mkSpell (.of .none)
    (.seq #[Instruction.drawFixed n, Instruction.discardFixed 1])
    s!"draw {cardPhrase n}, then discard a card"

def scry (n : Nat) : Effect :=
  mkSpell (.of .none)
    (Instruction.scryFixed n)
    s!"scry {n}"

/-- Tap the target, then scry `scryN` and draw `drawN` (Hithlain Knots).
The draw waits until the scry finishes. An illegal target means none of
the steps happen. -/
def tapScryDraw (scryN drawN : Nat) : Effect :=
  mkSpell (.of .creature)
    (.seq #[
      Instruction.tap (.target 0),
      Instruction.scryFixed scryN,
      Instruction.drawFixed drawN
    ])
    s!"tap target creature. Scry {scryN}. Draw {cardPhrase drawN}"

def tapOneOrTwoCreatures : Effect :=
  mkSpell (.of .creature)
    (Instruction.tap .allTargets)
    "tap one or two target creatures"
    (maxTargets := 2)

def grantHexproofIndestructible : Effect :=
  mkSpell (.of .artifactOrCreatureYouControl)
    (Instruction.grantKeywords (.target 0) #[Keyword.hexproof, Keyword.indestructible])
    "target artifact or creature you control gains hexproof and indestructible until end of turn"

/-- Put `counters` of `kind` on up to one target creature, then the targeted
player gains `life`. Defaults are one +1/+1 counter (Meager Meal). -/
def plusOneUpToOneAndPlayerGainsLife (life : Nat)
    (kind : CounterKind := .plusOnePlusOne) (counters : Nat := 1) : Effect :=
  mkSpell (.of .upToOneCreatureThenPlayer)
    (.seq #[
      Instruction.putCounters (.target 0) kind (.const (Int.ofNat counters)),
      Instruction.gainLifeFixed life (.target 1)
    ])
    s!"put {kind.countersPhrase counters} on up to one target creature. Target player gains {life} life"

def counterSpell : Effect :=
  mkSpell (.of .spell)
    (Instruction.counter (.target 0))
    "counter target spell"

/-- Counter the targeted spell unless its controller pays `{n}`. -/
def counterUnlessPays (n : Nat) : Effect :=
  mkSpell (.of .spell)
    (.unlessPays (.controllerOf (.target 0)) (CostSpec.ofGeneric n) (Instruction.counter (.target 0)))
    s!"counter target spell unless its controller pays \{{n}}"

def counterCreatureSpellPTAtMost (n : Nat) : Effect :=
  let spec := TargetSpec.creatureSpellPTAtMost n
  mkSpell (.of spec)
    (Instruction.counter (.target 0))
    s!"counter {spec.noun}"

def counterExilePermanentMayCast : Effect :=
  mkSpell (.of .spell)
    (Instruction.counter (.target 0) (exileInstead := true) (ifPermanentMayCastFree := true))
    "counter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled"

/-- The owner puts the targeted creature on the top or bottom of their library. -/
def putOnTopOrBottom : Effect :=
  mkSpell (.of .creature)
    (.moveZone (.target 0) (.library .owner .top true) .put {})
    "target creature's owner puts it on their choice of the top or bottom of their library"

def untapPumpMaybeAttach (power toughness : Int) : Effect :=
  let equipYouControl : ObjectExpr :=
    .inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .controlledBy .you])
  mkSpell (.of .creatureYouControl)
    (.seq #[
      Instruction.untap (.target 0),
      Instruction.pumpFixed (.target 0) power toughness,
      Instruction.ifThen (.exists (.filter (.target 0) (.hasSubtype (.literal .dwarf))))
        (Instruction.may .you none (.permanent (.attach equipYouControl (.target 0) true)))
    ])
    s!"untap target creature you control. It gets {signedStat power}/{signedStat toughness} until end of turn. If it's a Dwarf, you may attach an Equipment you control to it"

def exchangeControlSharingType : Effect :=
  mkSpell (.of .twoNonlandsSharingType)
    (.installEffect (.applyContinuous .indefinite (.target 0) (.exchangeControl (.target 1))))
    "exchange control of two target nonland permanents that share a card type"

def returnSpellDraw : Effect :=
  mkSpell (.of .spell)
    (.seq #[Instruction.bounce (.target 0), Instruction.drawFixed 1])
    "return target spell to its owner's hand. Draw a card"

def creaturesYouControlGet (power toughness : Int) : Effect :=
  mkSpell (.of .none)
    (Instruction.pumpFixed creaturesYouControlExpr power toughness)
    s!"creatures you control get {signedStat power}/{signedStat toughness} until end of turn"

def destroyArtifactOrEnchantmentGainLife (life : Nat) : Effect :=
  mkSpell (.of .artifactOrEnchantment)
    (.seq #[Instruction.destroy (.target 0), Instruction.gainLifeFixed life])
    s!"destroy target artifact or enchantment. You gain {life} life"

def destroyCreaturePowerAtLeast (n : Int) : Effect :=
  destroyTarget (.creaturePowerAtLeast n) (capitalize := false) (preferAsDefaultMode := true)

def becomeArtifactGainIndestructible : Effect :=
  mkSpell (.of .creature)
    (Instruction.becomeArtifactIndestructible (.target 0))
    "until end of turn, target creature becomes an artifact in addition to its other types and gains indestructible"

def pumpAndGrantKeywords (power toughness : Int) (k : Array KeywordAbility) : Effect :=
  mkSpell (.of .creature .own)
    (.seq #[
      Instruction.pumpFixed (.target 0) power toughness,
      Instruction.grantKeywords (.target 0) k
    ])
    s!"target creature gets {signedStat power}/{signedStat toughness} and gains {KeywordAbility.joinedAnd k} until end of turn"

def amassGoblins (n : Nat) : Effect :=
  mkSpell (.of .none)
    (Instruction.amassFixed n .goblin)
    s!"amass Goblins {n}"

def drawLoseLifeThenAmass (n : Nat) : Effect :=
  mkSpell (.of .none)
    (.seq #[Instruction.drawFixed 1, Instruction.loseLifeFixed 1, Instruction.amassFixed n .goblin])
    s!"you draw a card and lose 1 life. Amass Goblins {n}"

def returnCreatureFromGyThenAmass (n : Nat) : Effect :=
  mkSpell (.of .creatureCardInYourGraveyard)
    (.seq #[
      .moveZone (.target 0) (.hand .controller) .returnToHand {},
      Instruction.amassFixed n .goblin
    ])
    s!"return up to one target creature card from your graveyard to your hand. Amass Goblins {n}"
    (allowsZeroTargets := true)

/-- Counter the targeted spell. If its mana value was `n` or less, recruit.
The mana value includes `{X}` from when the spell was on the stack. -/
def counterThenRecruitIfMvAtMost (n : Nat) : Effect :=
  mkSpell (.of .spell)
    (.seq #[
      Instruction.counter (.target 0),
      Instruction.ifThen (.cmp .le (.objectStat .manaValue (.target 0)) (.const (Int.ofNat n)))
        Instruction.recruit
    ])
    s!"counter target spell. If that spell's mana value was {n} or less, recruit"

def plusOneThenFight (n : Nat) : Effect :=
  mkSpell (.of .creatureYouControlThenOppCreature)
    (.seq #[
      Instruction.putPlusOne (.target 0) n,
      .damage (.fight (.target 0) (.target 1) false)
    ])
    s!"put {CounterKind.plusOnePlusOne.countersPhrase n} on target creature you control. Then it fights target creature an opponent controls"

/-- Put a +1/+1 counter on the targeted creature you control. If this spell
was cast from a graveyard, also put one on each other creature you control. -/
def plusOneThenEachOtherIfFromGy : Effect :=
  let otherCreaturesYouControl : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .controlledBy .you, .otherThan (.target 0)])
  mkSpell (.of .creatureYouControl)
    (.seq #[
      Instruction.putPlusOne (.target 0) 1,
      Instruction.ifThen (.castPred (.castFrom .graveyard .this))
        (Instruction.putPlusOne otherCreaturesYouControl 1)
    ])
    "put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control"

/-- Draw `n` cards, or `fromGy` cards if this spell was cast from a graveyard. -/
def drawIfFromGy (n fromGy : Nat) : Effect :=
  mkSpell (.of .none)
    (.ifCond (.castPred (.castFrom .graveyard .this))
      (Instruction.drawFixed fromGy) (Instruction.drawFixed n))
    s!"draw {cardPhrase n}. If this spell was cast from a graveyard, draw {cardPhrase fromGy} instead"

/-- Amass Goblins `n`, or `fromGy` if this spell was cast from a graveyard. -/
def amassGoblinsOrFromGy (n fromGy : Nat) : Effect :=
  mkSpell (.of .none)
    (.ifCond (.castPred (.castFrom .graveyard .this))
      (Instruction.amassFixed fromGy .goblin) (Instruction.amassFixed n .goblin))
    s!"amass Goblins {n}. If this spell was cast from a graveyard, amass Goblins {fromGy} instead"

def searchLegendaryCreatureToHand : Effect :=
  mkSpell (.of .none)
    (.player (.searchLibrary {
      zones := .libraryOf .you
      filter := .all #[.hasSupertype .legendary, .hasType .creature]
      count := .upTo (.const 1)
      dest := .hand .controller
      reveal := true
      shuffle := true
    }))
    (searchLibraryToHandPhrase "a legendary creature card")

def dealDamageToEachOppCreature (n : Nat) : Effect :=
  mkSpell (.of .none)
    (Instruction.dealDamageFixed (.objects oppCreaturesExpr) n)
    s!"deals {n} damage to each creature your opponents control"

def destroyTargetArtifact : Effect :=
  destroyTarget .artifact (capitalize := false)

def targetPlayerDraw (n : Nat) : Effect :=
  mkSpell (.of .player .selfPlayer)
    (Instruction.drawFixed n (.target 0))
    s!"target player draws {cardPhrase n}"

def dealDamageToCreatureExileIfDies (n : Nat) : Effect :=
  mkSpell (.of .creature)
    (.seq #[
      Instruction.exileIfDiesThisTurn (.target 0),
      Instruction.dealDamageFixed (.targetSlot 0) n
    ])
    s!"deals {n} damage to target creature. If that creature would die this turn, exile it instead"

def destroyArtifactToken : Effect :=
  destroyTarget .artifactToken (capitalize := false)

def addRedPerOppArtifacts : Effect :=
  let oppArtifacts : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .artifact, .controlledBy .opponent])
  mkSpell (.of .none)
    (Instruction.addMana {
      spec := .sequence #[(.colored .red, .aggregate .count .one oppArtifacts)]
    })
    "add {R} for each artifact your opponents control"

def dealDamageToEachNonDragon (n : Nat) : Effect :=
  let nonDragons : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .not (.hasSubtype (.literal .dragon))])
  mkSpell (.of .none)
    (Instruction.dealDamageFixed (.objects nonDragons) n)
    s!"deals {n} damage to each non-Dragon creature"

def chooseTypeReturnOthers : Effect :=
  mkSpell (.of .none)
    (.bind ⟨0⟩ (.player (.choose .you .creatureType))
      (Instruction.bounce (.inZones .battlefield (.all #[
        .hasType .creature, .not (.hasSubtype (.fromStep ⟨0⟩))
      ]))))
    "choose a creature type. Return all creatures that aren't of the chosen type to their owners' hands"

def drawEqualToughnessThenPutCreatures : Effect :=
  mkSpell (.of .none)
    (.seq #[
      Instruction.draw (.aggregate .max (.stat .toughness) creaturesYouControlExpr),
      .moveZone (.inZones (.handOf .you) (.hasType .creature)) (.battlefield .controller) .put {
        choice? := some { chooser := .controller, count := .anyNumber }
      }
    ])
    "draw cards equal to the greatest toughness among creatures you control, then put any number of creature cards from your hand onto the battlefield"

def millThenPutInstantOrSorcery (n : Nat) : Effect :=
  mkSpell (.of .none)
    (.player (.inspectLibrary {
      source := .millCards .you (.const (Int.ofNat n))
      action := .takeMatching (.any #[.hasType .instant, .hasType .sorcery]) (.exact (.const 1))
        (.hand .controller)
      rest := .leaveInPlace
    }))
    s!"mill {n} cards, then put an instant or sorcery card from among them into your hand"

def millThenPutLands (n max : Nat) : Effect :=
  mkSpell (.of .none)
    (.player (.inspectLibrary {
      source := .millCards .you (.const (Int.ofNat n))
      action := .takeMatching (.hasType .land) (.upTo (.const (Int.ofNat max)))
        (.hand .controller)
      rest := .leaveInPlace
    }))
    s!"mill {n} cards, then put up to {englishNumber max} land cards from among them into your hand"

def exileThenReturnYouControl : Effect :=
  mkSpell (.of .twoCreaturesOrLandsYouControl)
    (.moveZone .allTargets .exile .exile {
      delayedReturn? := some (.immediately false .owner)
    })
    "exile two target creatures and/or lands you control, then return them to the battlefield under their owner's control"

def dealDamageToEachNonDragonThenAddDragonMana (n : Nat) : Effect :=
  let nonDragons : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .not (.hasSubtype (.literal .dragon))])
  mkSpell (.of .none)
    (.seq #[
      Instruction.dealDamageFixed (.objects nonDragons) n,
      Instruction.addMana {
        spec := .combination .anyColor (.const 4)
        restriction := some (.subtypeSpell .dragon)
      }
    ])
    s!"deals {n} damage to each non-Dragon creature. Add four mana in any combination of colors. Spend this mana only to cast Dragon spells"

def millThenPutAllInstantsOrSorceries (n : Nat) : Effect :=
  mkSpell (.of .none)
    (.player (.inspectLibrary {
      source := .millCards .you (.const (Int.ofNat n))
      action := .takeMatching (.any #[.hasType .instant, .hasType .sorcery]) .anyNumber
        (.hand .controller)
      rest := .leaveInPlace
    }))
    s!"mill {n} cards, then put all instant and sorcery cards from among them into your hand"

def exileAttackersSearchBasics : Effect :=
  let targetPlayerAttackers : ObjectExpr :=
    .inZones .battlefield (.all #[
      .hasType .creature, .combatRole .attacking, .controlledBy (.ofExpr (.target 0))
    ])
  mkSpell (.of .player)
    (.bind ⟨0⟩ (Instruction.exile targetPlayerAttackers)
      (Instruction.may (.target 0) none
        (.player (.searchLibrary {
          searcher := .target 0
          zones := .libraryOf (.target 0)
          filter := .all #[.hasSupertype .basic, .hasType .land]
          count := .upTo (.stepMetric .movedCount ⟨0⟩)
          dest := .battlefield (.player (.target 0))
          mods := { tapped := true }
          reveal := false
          shuffle := true
        }))))
    "exile all attacking creatures target player controls. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle"

def createTokensX (kind : TokenSpec) : Effect :=
  mkSpell (.of .none)
    (Instruction.createTokens kind .chosenX)
    s!"create X {kind.pluralNoun}"

def exileTopPlayIfYouControlSubtype (n : Nat) (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  mkSpell (.of .none)
    (.moveZone (.topOfLibrary .you (.const (Int.ofNat n))) .exile .exile {
      enterFaceDown := true
      grantPlayPerm? := some {
        duration := .indefinite
        landsAllowed := true
        condition? := some (.exists (.inZones .battlefield (.all #[
          .hasSubtype (.literal sub), .controlledBy .you
        ])))
      }
    })
    s!"look at the top {n} cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a {sub}"

def returnSpellCantCastIfGift : Effect :=
  mkSpell (.of .spell)
    (.seq #[
      Instruction.bounce (.target 0),
      Instruction.ifThen (.castPred (.giftPromised .this))
        (.installEffect (.applyRule .untilEndOfTurn (.player (.cantCastSpells .any .anyObject))))
    ])
    "return target spell to its owner's hand. If the gift was promised, players can't cast spells this turn"

def exileTopXOppPlayForLife : Effect :=
  mkSpell (.of .opponent)
    (.moveZone (.topOfLibrary (.target 0) .chosenX) .exile .exile {
      grantPlayPerm? := some {
        duration := .untilEndOfTurn
        landsAllowed := true
        payLifeInsteadOfMana := true
      }
    })
    "exile the top X cards of target opponent's library. You may play those cards this turn. If you cast a spell this way, pay life equal to its mana value rather than pay its mana cost"

def riddlesInTheDark : Effect :=
  mkSpell (.of .none)
    (.player (.inspectLibrary {
      source := .topCards .you (.const 4) false
      action := .splitIntoPiles .you .opponents 2 (.hand .controller) .graveyard
      rest := .leaveInPlace
    }))
    "look at the top four cards of your library and separate them into a face-down pile and a face-up pile. An opponent chooses one of the piles. Put that pile into your hand and the other into your graveyard"

def supperForSpiders : Effect :=
  mkSpell (.of .none)
    (.moveZone
      (.inZones (.graveyardOf .opponents) (.all #[.hasType .creature, .putIntoGraveyardFromBattlefieldThisTurn]))
      (.battlefield .controller) .put {
        enterTypeMod? := some { types := #[.artifact], subtypes := #[.food] }
        enterAsPredefined? := some .food
      })
    "put onto the battlefield under your control all creature cards in your opponents' graveyards that were put there from the battlefield this turn. They are Food artifacts with \"{2}, {T}, Sacrifice this artifact: You gain 3 life.\""

def eaglesAreComing : Effect :=
  mkSpell (.of (.ofDomain (.object .battlefield (.all #[.hasType .creature, .ownedBy .you]))))
    (.bind ⟨0⟩ (Instruction.bounce .allTargets)
      (.installEffect (.createDelayedTrigger {
        pattern := .stepEachUpkeep
        duration := .indefinite
        oneShot := true
        effect := {
          body := Instruction.createTokens .birdSoldier (.stepMetric .movedCount ⟨0⟩)
        }
      })))
    "choose target creature you own. If this spell was kicked, instead choose any number of target creatures you own. Return each chosen creature to your hand. At the beginning of the next upkeep, create a 4/4 white Bird Soldier creature token with flying for each creature returned to your hand this way"

def lookAtTopLandsGainLife (n life : Nat) : Effect :=
  mkSpell (.of .none)
    (.seq #[
      .player (.inspectLibrary {
        source := .topCards .you (.const (Int.ofNat n)) false
        action := .takeMatching (.hasType .land) .anyNumber (.battlefield .controller) { tapped := true }
        rest := .shuffleIntoLibrary
      }),
      Instruction.gainLifeFixed life
    ])
    s!"look at the top {n} cards of your library, put any number of land cards from among them onto the battlefield tapped, then shuffle. You gain {life} life"

def gainControlOppArtifacts : Effect :=
  mkSpell (.of (.forEachOpponentControlled (.hasType .artifact) (.upTo 1)))
    (.installEffect (.applyContinuous .indefinite .allTargets (.gainControl .you)))
    "for each opponent, gain control of up to one target artifact that player controls"
    (allowsZeroTargets := true)

def damageOppCreaturesEqualOtherSpellsMv : Effect :=
  mkSpell (.of .none)
    (Instruction.dealDamage (.objects oppCreaturesExpr)
      (.playerMetric .otherSpellsManaValueThisTurn .you))
    "deals damage to each creature your opponents control equal to the total mana value of other spells you've cast this turn"

def phaseOutKicker : Effect :=
  let targetCtrlCreatures : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .controlledBy (.ofExpr (.target 0))])
  mkSpell (.of .creature)
    (.ifCond (.castPred (.wasKicked .this))
      (.permanent (.phaseOut targetCtrlCreatures none))
      (.permanent (.phaseOut (.target 0) none)))
    "target creature phases out. If this spell was kicked, each creature target player controls phases out instead"

def dealDamageToAttackerOrBlocker (n teamworkN : Nat) : Effect :=
  mkSpell (.of .attackingOrBlockingCreature)
    (.ifCond (.castPred (.teamworkPaid .this))
      (Instruction.dealDamageFixed (.targetSlot 0) teamworkN)
      (Instruction.dealDamageFixed (.targetSlot 0) n))
    s!"deals {n} damage to target attacking or blocking creature. If this spell was cast using teamwork, it deals {teamworkN} damage to that creature instead"

def dealDamageThenControllerIfTeamwork (n extra : Nat) : Effect :=
  mkSpell (.of .creature)
    (.seq #[
      Instruction.dealDamageFixed (.targetSlot 0) n,
      Instruction.ifThen (.castPred (.teamworkPaid .this))
        (Instruction.dealDamageFixed (.players (.controllerOf (.target 0))) extra)
    ])
    s!"deals {n} damage to target creature. If this spell was cast using teamwork, it also deals {extra} damage to that creature's controller"

def grantDoubleStrikeTeamworkTrample : Effect :=
  mkSpell (.of .creature)
    (.seq #[
      Instruction.grantKeywords (.target 0) #[Keyword.doubleStrike],
      Instruction.ifThen (.castPred (.teamworkPaid .this))
        (Instruction.grantKeywords (.target 0) #[Keyword.trample])
    ])
    "target creature gains double strike until end of turn. If this spell was cast using teamwork, that creature also gains trample until end of turn"

def counterUnlessPaysTeamwork (n teamworkN : Nat) : Effect :=
  mkSpell (.of .spell)
    (.ifCond (.castPred (.teamworkPaid .this))
      (.unlessPays (.controllerOf (.target 0)) (CostSpec.ofGeneric teamworkN) (Instruction.counter (.target 0)))
      (.unlessPays (.controllerOf (.target 0)) (CostSpec.ofGeneric n) (Instruction.counter (.target 0))))
    s!"counter target spell unless its controller pays \{{n}}. Counter that spell unless its controller pays \{{teamworkN}} instead if this spell was cast using teamwork"

def exileCreatureMvAtMostOrAnyIfTeamwork (n life : Nat) : Effect :=
  mkSpell (.of (.creatureMvAtMostOrAnyIfTeamwork n))
    (.ifCond (.castPred (.teamworkPaid .this))
      (.seq #[Instruction.exile (.target 0), Instruction.gainLifeFixed life])
      (Instruction.exile (.target 0)))
    s!"exile target creature with mana value {n} or less. If this spell was cast using teamwork, instead exile target creature and you gain {life} life"

def returnGyCreatureMvAtMostOrAny (n : Nat) : Effect :=
  mkSpell (.of (.creatureCardInYourGraveyardMvAtMostOrAnyIfTeamwork n))
    (.moveZone (.target 0) (.battlefield .controller) .put {})
    s!"choose target creature card in your graveyard with mana value {n} or less. If this spell was cast using teamwork, instead choose target creature card in your graveyard. Return the chosen card to the battlefield"

def revealTopPutCreatures (n : Nat) : Effect :=
  mkSpell (.of .none)
    (.ifCond (.castPred (.teamworkPaid .this))
      (.player (.inspectLibrary {
        source := .topCards .you (.const (Int.ofNat n)) true
        action := .takeMatching (.hasType .creature) .anyNumber (.battlefield .controller)
        rest := .graveyard
      }))
      (.player (.inspectLibrary {
        source := .topCards .you (.const (Int.ofNat n)) true
        action := .takeMatching (.hasType .creature) (.upTo (.const 1)) (.battlefield .controller)
        rest := .graveyard
      })))
    s!"reveal the top {n} cards of your library. You may put a creature card from among them onto the battlefield. If this spell was cast using teamwork, put any number of creature cards from among them onto the battlefield instead. Put the rest into your graveyard"

def createTokens (kind : TokenSpec) (n : Nat) : Effect :=
  mkSpell (.of .none)
    (Instruction.createTokensFixed kind n)
    (TokenSpec.createPhrase kind n)

def exileCreatureToughnessAtLeast (n : Int) : Effect :=
  let spec := TargetSpec.creatureToughnessAtLeast n
  mkSpell (.of spec)
    (Instruction.exile (.target 0))
    s!"exile {spec.noun}"

def exileEnchantmentMvAtLeast (n : Nat) : Effect :=
  let spec := TargetSpec.enchantmentMvAtLeast n
  mkSpell (.of spec)
    (Instruction.exile (.target 0))
    s!"exile {spec.noun}"

def returnOneOrTwoNonlands : Effect :=
  mkSpell (.of .nonland)
    (Instruction.bounce .allTargets)
    "return one or two target nonland permanents to their owners' hands"
    (maxTargets := 2)

def grantDeathtouch : Effect :=
  mkSpell (.of .creature)
    (Instruction.grantKeywords (.target 0) #[Keyword.deathtouch])
    "target creature gains deathtouch until end of turn"

def destroyNoncreatureArtifact : Effect :=
  destroyTarget .noncreatureArtifact (capitalize := false)

def plusOneOnCreature : Effect :=
  mkSpell (.of .creature)
    (Instruction.putPlusOne (.target 0) 1)
    "put a +1/+1 counter on target creature"

def targetPlayerCreatesTokens (kind : TokenSpec) (n : Nat) : Effect :=
  mkSpell (.of .player)
    (Instruction.createTokensFixed kind n (.target 0))
    s!"target player creates {TokenSpec.createdTokensPhrase kind n}"

def destroyCreatureSurveil : Effect :=
  mkSpell (.of .creature)
    (.seq #[Instruction.destroy (.target 0), Instruction.surveilFixed 1])
    "destroy target creature. Surveil 1"

def investigatePumpFlyingUntap : Effect :=
  mkSpell (.of .playerThenCreature)
    (.seq #[
      Instruction.createTokensFixed .clue 1 (.target 0),
      Instruction.grantKeywords (.target 1) #[Keyword.flying],
      Instruction.untap (.target 1),
      Instruction.pumpFixed (.target 1) 1 0
    ])
    "target player investigates. Target creature gets +1/+0 and gains flying until end of turn. Untap it"

def plusOneLifelinkIndestructible : Effect :=
  mkSpell (.of .creature)
    (.seq #[
      Instruction.putPlusOne (.target 0) 1,
      Instruction.grantKeywords (.target 0) #[Keyword.lifelink, Keyword.indestructible]
    ])
    "put a +1/+1 counter on target creature. It gains lifelink and indestructible until end of turn"

def dealDamageToEachCreature (n : Nat) : Effect :=
  mkSpell (.of .none)
    (Instruction.dealDamageFixed (.objects allCreaturesExpr) n)
    s!"deals {n} damage to each creature"

def destroyLandSearchBasic : Effect :=
  mkSpell (.of .artifactOrLand)
    (.seq #[
      Instruction.destroy (.target 0),
      Instruction.may (.controllerOf (.target 0)) none
        (.player (.searchLibrary {
          searcher := .controllerOf (.target 0)
          zones := .libraryOf (.controllerOf (.target 0))
          filter := .all #[.hasSupertype .basic, .hasType .land]
          count := .upTo (.const 1)
          dest := .battlefield (.player (.controllerOf (.target 0)))
          mods := { tapped := true }
          reveal := false
          shuffle := true
        }))
    ])
    "destroy target artifact or land. Its controller may search their library for a basic land card, put it onto the battlefield tapped, then shuffle"

def doublePowerAndToughness : Effect :=
  mkSpell (.of .creature)
    (Instruction.doublePT (.target 0))
    "double target creature's power and toughness until end of turn"

def returnGySubtypeToHand (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  mkSpell (.of (.ofDomain (.object .yourGraveyard (.all #[.hasSubtype (.literal sub), .isKind .card]))))
    (.moveZone (.target 0) (.hand .controller) .returnToHand {})
    s!"return target {sub} card from your graveyard to your hand"

def grantVigilanceUnblockable : Effect :=
  mkSpell (.of .creature)
    (.seq #[
      Instruction.grantKeywords (.target 0) #[Keyword.vigilance],
      Instruction.cantBeBlocked (.target 0),
      Instruction.drawFixed 1
    ])
    "target creature gains vigilance until end of turn and can't be blocked this turn"

def becomeArtifactCreature44Flying : Effect :=
  mkSpell (.of .artifactOrCreatureYouControl)
    (.installEffect (.applyContinuous .untilEndOfTurn (.target 0)
      (.all #[
        .modifyTypes { types := #[.artifact, .creature] },
        .setBasePT (some (.const 4)) (some (.const 4)),
        .grantKeywords #[Keyword.flying]
      ])))
    "until end of turn, target artifact or creature you control becomes an artifact creature with base power and toughness 4/4 and gains flying"

def drawThreeDiscardUnlessArtifact : Effect :=
  mkSpell (.of .none)
    (.seq #[
      Instruction.drawFixed 3,
      .moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard {
        choice? := some {
          chooser := .controller
          count := .exact (.const 2)
          unlessMatching? := some (.hasType .artifact)
        }
      }
    ])
    "draw three cards. Then discard two cards unless you discard an artifact card"

def eachOpponentLosesLife (n : Nat) : Effect :=
  mkSpell (.of .none)
    (Instruction.loseLifeFixed n .opponents)
    s!"each opponent loses {n} life"

def fight : Effect :=
  mkSpell (.of .creatureYouControlThenOppCreature)
    (.damage (.fight (.target 0) (.target 1) false))
    "target creature you control fights target creature an opponent controls"

def fightUpToOne : Effect :=
  mkSpell (.of .creatureYouControlThenOppCreature)
    (.damage (.fight (.target 0) (.target 1) false))
    "target creature you control fights up to one other target creature"
    (allowsZeroTargets := true)

def plusOneOnEachYouControl : Effect :=
  mkSpell (.of .none)
    (Instruction.putPlusOne creaturesYouControlExpr 1)
    "put a +1/+1 counter on each creature you control"

def plusOneOnCreatureN (n : Nat) : Effect :=
  mkSpell (.of .creatureYouControl)
    (Instruction.putPlusOne (.target 0) n)
    s!"put {plusOnePlusOneCountersPhrase n} on target creature you control"

def pumpThenDraw (power toughness : Int) : Effect :=
  let tStr := if toughness == 0 && power < 0 then "-0" else signedStat toughness
  mkSpell (.of .creature)
    (.seq #[Instruction.pumpFixed (.target 0) power toughness, Instruction.drawFixed 1])
    s!"Target creature gets {signedStat power}/{tStr} until end of turn.\nDraw a card."

def pumpThenExileTopPlay (power toughness : Int) : Effect :=
  mkSpell (.of .creature)
    (.seq #[
      Instruction.pumpFixed (.target 0) power toughness,
      .moveZone (.topOfLibrary .you (.const 1)) .exile .exile {
        grantPlayPerm? := some { duration := .untilEndOfNextTurnOf .you, landsAllowed := true }
      }
    ])
    s!"Target creature gets {signedStat power}/{signedStat toughness} until end of turn.\nExile the top card of your library. {playThatCardUntilNextTurnPhrase}."

def creatureYouControlDealsTwicePower (k : Nat := 2) : Effect :=
  let dmg : ValueExpr :=
    if k == 1 then .objectStat .power (.target 0)
    else .binary .mul (.const (Int.ofNat k)) (.objectStat .power (.target 0))
  mkSpell (.of .creatureYouControlThenOppCreature)
    (Instruction.dealDamage (.targetSlot 1) dmg (.target 0))
    s!"Target creature you control deals damage equal to {timesPhrase k} its power to target creature an opponent controls."

def createTokensThenTeamPump (kind : TokenSpec) (n : Nat) (power toughness : Int) : Effect :=
  let tokens := capitalizeAscii (TokenSpec.createPhrase kind n)
  mkSpell (.of .none)
    (.seq #[
      Instruction.createTokensFixed kind n,
      Instruction.pumpFixed creaturesYouControlExpr power toughness
    ])
    s!"{tokens}, then creatures you control get {signedStat power}/{signedStat toughness} until end of turn."

def createTokensPerSubtype (kind : TokenSpec) (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  let cnt : ValueExpr :=
    .aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal sub), .controlledBy .you]))
  mkSpell (.of .none)
    (Instruction.createTokens kind cnt)
    s!"Create a {kind.oracleNoun} for each {sub} you control"

def creaturesYouControlGetAndGrant (power toughness : Int) (k : Array KeywordAbility) : Effect :=
  mkSpell (.of .none)
    (.seq #[
      Instruction.pumpFixed creaturesYouControlExpr power toughness,
      Instruction.grantKeywords creaturesYouControlExpr k
    ])
    s!"Creatures you control get {signedStat power}/{signedStat toughness} and gain {KeywordAbility.joinedAnd k} until end of turn"

def destroyUpToOneNonland : Effect :=
  mkSpell (.of .nonland)
    (Instruction.destroy (.target 0))
    "Destroy up to one target nonland permanent"
    (allowsZeroTargets := true)

def createGalactus : Effect :=
  mkSpell (.of .none)
    (Instruction.createTokensFixed .galactus 1)
    "Create Galactus, a legendary 16/16 black Elder Alien creature token with flying, trample, and \"Whenever Galactus attacks, destroy target land.\""

def worldsWithinWorlds : Effect :=
  mkSpell (.of .none)
    (.bind ⟨0⟩ (Instruction.exile allCreaturesExpr)
      (.seq #[
        .forEach (.eachPlayer .any) ⟨1⟩
          (.moveZone (.inZones (.handOf (.stepPlayers ⟨1⟩)) (.hasType .creature))
            (.battlefield (.player (.stepPlayers ⟨1⟩))) .put {
              choice? := some { chooser := .player (.stepPlayers ⟨1⟩), count := .anyNumber }
            }),
        .moveZone (.stepObjects ⟨0⟩) (.hand .owner) .put {},
        .installEffect (.applyReplacement .untilEndOfTurn .exileOnLeaveStack)
      ]))
    "Exile all creatures. Each player may put any number of creature cards from their hand onto the battlefield. Then put all cards exiled this way into their owners' hands. Exile Worlds Within Worlds."

def exileHandDrawPlayUntilNext : Effect :=
  mkSpell (.of .none)
    (.bind ⟨0⟩ (.moveZone (.inZones (.handOf .you) .anyObject) .exile .exile {
        grantPlayPerm? := some { duration := .untilEndOfNextTurnOf .you, landsAllowed := true }
      })
      (Instruction.draw (.stepMetric .movedCount ⟨0⟩)))
    "Exile all the cards from your hand, then draw that many cards. Until the end of your next turn, you may play cards exiled this way."

def copyNontokenCreaturesYouControl : Effect :=
  let nontokenCreatures : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .controlledBy .you, .isToken false])
  mkSpell (.of .none)
    (.forEach (.eachObject nontokenCreatures) ⟨0⟩
      (Instruction.createTokens (.copyOf (.stepObjects ⟨0⟩) #[.removeSupertype .legendary])))
    "For each nontoken creature you control, create a token that's a copy of that creature, except it isn't legendary."

def gainControlUntilEotOrNextIfVillain : Effect :=
  let biggerVillain : Condition :=
    .exists (.inZones .battlefield (.all #[
      .hasSubtype (.literal .villain),
      .controlledBy .you,
      .stat .manaValue .gt (.objectStat .manaValue (.target 0))
    ]))
  mkSpell (.of .creature)
    (.seq #[
      .ifCond biggerVillain
        (.installEffect (.applyContinuous (.untilEndOfNextTurnOf .you) (.target 0) (.gainControl .you)))
        (.installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.gainControl .you))),
      Instruction.untap (.target 0),
      Instruction.grantKeywords (.target 0) #[Keyword.haste]
    ])
    "Gain control of target creature until end of turn. If you control a Villain with greater mana value than that creature, gain control of that creature until the end of your next turn instead. Untap that creature. It gains haste until end of turn."

def millThenPutPermanentGainLife (n life : Nat) : Effect :=
  mkSpell (.of .none)
    (.seq #[
      .player (.inspectLibrary {
        source := .millCards .you (.const (Int.ofNat n))
        action := .takeMatching (.isKind .permanentCard) (.upTo (.const 1)) (.hand .controller)
        rest := .leaveInPlace
      }),
      Instruction.gainLifeFixed life
    ])
    s!"Mill {n} cards. You may put a permanent card from among the milled cards into your hand. You gain {life} life."

def searchLibraryOrGyArtifactCreatureX : Effect :=
  mkSpell (.of .none)
    (.bind ⟨0⟩ (.player (.searchLibrary {
        zones := { zones := #[.library, .graveyard], owner := .ofPlayer .you }
        filter := .all #[.hasType .artifact, .hasType .creature, .stat .manaValue .le .chosenX]
        count := .upTo (.const 1)
        dest := .battlefield .controller
        mods := { enterCounters := #[(.plusOnePlusOne, .chosenX)] }
        reveal := false
        shuffle := true
      }))
      (Instruction.ifThen (.cmp .ge .chosenX (.const 4))
        (Instruction.grantKeywords (.stepObjects ⟨0⟩) #[Keyword.haste])))
    "Search your library and/or graveyard for an artifact creature card with mana value X or less and put it onto the battlefield with X additional +1/+1 counters on it. If X is 4 or greater, it gains haste until end of turn. If you search your library this way, shuffle."

def gainLifeSearchBasicPlusOne (life : Nat) : Effect :=
  mkSpell (.of .upToOneCreatureThenPlayer)
    (.seq #[
      Instruction.gainLifeFixed life (.target 1),
      .player (.searchLibrary {
        searcher := .target 1
        zones := .libraryOf (.target 1)
        filter := .all #[.hasSupertype .basic, .hasType .land]
        count := .upTo (.const 1)
        dest := .battlefield (.player (.target 1))
        mods := { tapped := true }
        reveal := false
        shuffle := true
      }),
      Instruction.putPlusOne (.target 0) 1
    ])
    s!"Target player gains {life} life, then searches their library for a basic land card, puts it onto the battlefield tapped, then shuffles. Put a +1/+1 counter on up to one target creature."

def nextFreeRGCreature : Effect :=
  mkSpell (.of .none)
    (.installEffect (.applyRule .untilEndOfTurn
      (.costMod
        (.spells .you (.all #[
          .hasType .creature,
          .any #[.hasColor (.literal .red), .hasColor (.literal .green)]
        ]))
        .alternativeFree true)))
    "The next red or green creature spell you cast this turn can be cast without paying its mana cost"

def ownerPutsLibraryThenConnive : Effect :=
  mkSpell (.of .oppCreatureThenUpToOneCreatureYouControl)
    (.seq #[
      .moveZone (.target 0) (.library .owner (.fromTop (.const 2)) true) .put {},
      .player (.connive (.target 1))
    ])
    "The owner of target creature an opponent controls puts it into their library second from the top or on the bottom. Then up to one target creature you control connives."

def copyThisSpellXTimesThenDamage (n : Nat) : Effect :=
  mkSpell (.of .creature)
    (Instruction.dealDamageFixed (.targetSlot 0) n)
    s!"When you cast this spell, copy it X times. You may choose new targets for the copies.\ndeals {n} damage to target creature."

def mayDrawPerArtifactOppsDraw : Effect :=
  let artifactsCount : ValueExpr :=
    .aggregate .count .one (.inZones .battlefield (.all #[.hasType .artifact, .controlledBy .you]))
  mkSpell (.of .none)
    (Instruction.may .you none
      (.seq #[
        Instruction.draw artifactsCount,
        Instruction.drawFixed 1 .opponents
      ]))
    "You may draw a card for each artifact you control. If you do, each opponent draws a card"

def mayPutHeroMvOrDraw (n : Nat) : Effect :=
  mkSpell (.of .none)
    (.bind ⟨0⟩ (Instruction.may .you none
        (.moveZone (.inZones (.handOf .you) (.all #[
            .hasSubtype (.literal .hero),
            .hasType .creature,
            .stat .manaValue .le (.const (Int.ofNat n))
          ])) (.battlefield .controller) .put {
            choice? := some { chooser := .controller, count := .exact (.const 1) }
          }))
      (Instruction.ifThen (.not (.stepSucceeded ⟨0⟩)) (Instruction.drawFixed 1)))
    s!"You may put a Hero creature card with mana value {n} or less from your hand onto the battlefield. If you don't, draw a card"

def maySacArtifactOrDiscardDraw (cards : Nat) : Effect :=
  mkSpell (.of .none)
    (Instruction.may .you (some CostSpec.sacrificeArtifactOrDiscardCard)
      (Instruction.drawFixed cards))
    s!"You may sacrifice an artifact or discard a card. If you do, draw {cardPhrase cards}."

def chooseTargetDoubleAndTrample : Effect :=
  mkSpell (.of .creatureYouControl)
    (.seq #[
      Instruction.doublePT (.target 0),
      Instruction.grantKeywords (.target 0) #[Keyword.trample]
    ])
    "Choose target creature you control. Until end of turn, double its power and toughness and it gains trample"

def returnUpToTwoGyModal : Effect :=
  mkSpell (.of (.single {
      domain := .object .yourGraveyard (.all #[
        .any #[.hasType .artifact, .hasType .creature, .hasType .enchantment, .hasType .land],
        .isKind .card])
      count := .upTo 2 }))
    (.moveZone .allTargets (.hand .controller) .returnToHand {})
    "Choose up to two. Return those cards from your graveyard to your hand. • Target artifact card. • Target creature card. • Target enchantment card. • Target land card."
    (maxTargets := 2) (allowsZeroTargets := true)

def artifactSpellsCostLessThisTurn (n : Nat) : Effect :=
  mkSpell (.of .none)
    (.installEffect (.applyRule .untilEndOfTurn
      (.costMod (.spells .you (.hasType .artifact)) (.reduceGeneric (.const (Int.ofNat n))))))
    s!"Artifact spells you cast this turn cost \{{n}} less to cast"

def supertypeSpellsCostLessThisTurn (n : Nat) : Effect :=
  mkSpell (.of .none)
    (.installEffect (.applyRule .untilEndOfTurn
      (.costMod (.spells .you (.hasSupertype .legendary)) (.reduceGeneric (.const (Int.ofNat n))))))
    s!"Legendary spells you cast this turn cost \{{n}} less to cast"

/-! ### Printed Activated-Ability Effect Constructors -/

def searchBasicLandTapped : Effect :=
  mkAbility ({})
    (.player (.searchLibrary {
      zones := .libraryOf .you
      filter := .all #[.hasSupertype .basic, .hasType .land]
      count := .upTo (.const 1)
      dest := .battlefield .controller
      mods := { tapped := true }
      reveal := false
      shuffle := true
    }))
    (capitalizeAscii (searchBasicLandTappedPhrase "your"))

def searchLandTypeFilter (landType : String) : ObjectPred :=
  if landType == "Basic land" || landType == "basic land" then
    .all #[.hasSupertype .basic, .hasType .land]
  else
    match Supertype.ofOracle? landType with
    | some sup => .hasSupertype sup
    | none =>
      match CardType.ofOracle? landType with
      | some ty => .hasType ty
      | none => .hasSubtype (.literal (CardSubtype.ofOracleD landType))

def searchLandTypeToHand (landType : String) : Effect :=
  mkAbility ({})
    (.player (.searchLibrary {
      zones := .libraryOf .you
      filter := searchLandTypeFilter landType
      count := .upTo (.const 1)
      dest := .hand .controller
      reveal := true
      shuffle := true
    }))
    (capitalizeAscii (searchLibraryToHandPhrase s!"a {landType} card"))

def exileTopPlayUntilEndOfNextTurn : Effect :=
  mkAbility ({})
    (.moveZone (.topOfLibrary .you (.const 1)) .exile .exile {
      grantPlayPerm? := some { duration := .untilEndOfNextTurnOf .you, landsAllowed := true }
    })
    "Exile the top card of your library. You may play it until the end of your next turn"

def dealDamageToTargetCreature (amount : Nat) : Effect :=
  mkAbility (.of .creature)
    (Instruction.dealDamageFixed (.targetSlot 0) amount)
    s!"This creature deals {amount} damage to target creature"

def destroyTargetColorlessNonland : Effect :=
  destroyTarget .colorlessNonland (capitalize := true)

def attachToTargetCreatureYouControl : Effect :=
  mkAbility (.of .creatureYouControl)
    (.permanent (.attach .this (.target 0)))
    "Attach this Equipment to target creature you control"

/-- Equip effect with optional subtype or worthy target restriction (CR 702.6c). -/
def equipEffect (subtype : Option CardSubtype := none) (worthy : Bool := false) : Effect :=
  let spec : TargetSpec :=
    if worthy then .worthyCreatureYouControl
    else match subtype with
      | some s => .creatureYouControlSubtype s
      | none => .creatureYouControl
  mkAbility (.of spec)
    (.permanent (.attach .this (.target 0)))
    s!"Attach this Equipment to {spec.noun}"

def becomeSubtypeWithLandsPT (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  let landsCount : ValueExpr :=
    .aggregate .count .one (.inZones .battlefield (.all #[.hasType .land, .controlledBy .you]))
  mkAbility ({})
    (.installEffect (.applyContinuous .indefinite .this
      (.all #[
        .modifyTypes { types := #[.creature], subtypes := #[sub] },
        .grantStatic #[.characteristicDefining (.setPT landsCount landsCount)]
      ])))
    s!"This enchantment becomes {indefinite sub.englishName} {sub} creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\""

def becomeBearCreatureWithLandsPT : Effect :=
  becomeSubtypeWithLandsPT "Bear"

def sourceGets (power toughness : Int) : Effect :=
  mkAbility ({})
    (Instruction.pumpFixed .this power toughness)
    s!"This creature gets {signedStat power}/{signedStat toughness} until end of turn"

def putPlusOnePlusOneOnSource (n : Nat) : Effect :=
  mkAbility ({})
    (Instruction.putPlusOne .this n)
    s!"Put {plusOnePlusOneCountersPhrase n} on this creature"

def targetCantBeBlockedThisTurn : Effect :=
  mkAbility (.of .creature .own)
    (Instruction.cantBeBlocked (.target 0))
    "Target creature can't be blocked this turn"

def returnFromGraveyardTapped : Effect :=
  mkAbility ({})
    (.moveZone .this (.battlefield .controller) .put { tapped := true })
    "Return this card from your graveyard to the battlefield tapped"

def returnFromGraveyardToHand : Effect :=
  mkAbility ({})
    (.moveZone .this (.hand .owner) .returnToHand {})
    "Return this card from your graveyard to your hand"

def destroyTargetArtifactOrEnchantment : Effect :=
  destroyTarget .artifactOrEnchantment (capitalize := true)

def millPlayer (n : Nat) : Effect :=
  mkAbility (.of .player)
    (Instruction.millFixed n (.target 0))
    s!"target player mills {n} cards"

def addAnyColor : Effect :=
  mkAbility ({})
    (Instruction.addMana { spec := .oneOf .anyColor (.const 1) })
    "Add one mana of any color"

def destroyTargetPermanent : Effect :=
  destroyTarget .permanent (capitalize := true)

def plusOneOnTarget (n : Nat) (subtypes : Array String := #[]) : Effect :=
  let spec : TargetSpec :=
    if subtypes.isEmpty then .creatureYouControl
    else .creatureYouControlAnySubtype (CardSubtype.ofSubtypes subtypes)
  mkAbility (.of spec)
    (Instruction.putPlusOne (.target 0) n)
    s!"Put {plusOnePlusOneCountersPhrase n} on {spec.noun}"

def targetCantBeBlockedPowerAtMost (n : Int) : Effect :=
  let spec := TargetSpec.creaturePowerAtMost n
  mkAbility (.of spec)
    (Instruction.cantBeBlocked (.target 0))
    s!"{capitalizeAscii spec.noun} can't be blocked this turn"

def recruit : Effect :=
  mkAbility ({})
    Instruction.recruit
    "Recruit"

def gainLife (n : Nat) : Effect :=
  mkAbility ({})
    (Instruction.gainLifeFixed n)
    s!"You gain {n} life"

def ownerShuffleSourceDraw (n : Nat) : Effect :=
  mkAbility ({})
    (.bind ⟨0⟩
      (.moveZone .this (.library .owner .bottom false) .shuffleIntoLibrary { shuffleAfter := true })
      (Instruction.ifThen (.stepSucceeded ⟨0⟩) (Instruction.drawFixed n (.ownerOf .this))))
    s!"This owner shuffles him into their library and draws {cardPhrase n}"

def returnFromGyAttachPowerAtMost (n : Int) : Effect :=
  let spec := TargetSpec.creatureYouControlPowerAtMost n
  mkAbility (.of spec)
    (.moveZone .this (.battlefield .controller) .put { attachTo? := some (.target 0) })
    s!"Return this card from your graveyard to the battlefield attached to {spec.noun}"

def addMana (types : Array ManaType) : Effect :=
  mkAbility ({})
    (Instruction.addSimpleMana types)
    s!"Add {manaSymbolsText types}"

def searchBasicLandToHand : Effect :=
  mkAbility ({})
    (.player (.searchLibrary {
      zones := .libraryOf .you
      filter := .all #[.hasSupertype .basic, .hasType .land]
      count := .upTo (.const 1)
      dest := .hand .controller
      reveal := true
      shuffle := true
    }))
    (capitalizeAscii (searchLibraryToHandPhrase "a basic land card"))

def searchTwoBasicsSplit : Effect :=
  mkAbility ({})
    (.player (.searchLibrary {
      zones := .libraryOf .you
      filter := .all #[.hasSupertype .basic, .hasType .land]
      count := .upTo (.const 2)
      dest := .battlefield .controller
      mods := { tapped := true }
      secondDest? := some (.hand .controller, {})
      reveal := true
      shuffle := true
    }))
    "Search your library for up to two basic land cards, reveal them, put one onto the battlefield tapped and the other into your hand, then shuffle"

def creaturesYouControlGetOppsLoseLife (power toughness : Int) (life : Nat) : Effect :=
  mkAbility ({})
    (.seq #[
      Instruction.pumpFixed creaturesYouControlExpr power toughness,
      Instruction.loseLifeFixed life .opponents
    ])
    s!"Creatures you control get {signedStat power}/{signedStat toughness} until end of turn. Each opponent loses {life} life"

def subtypesGainMenace (subtypes : Array String) : Effect :=
  let subs := CardSubtype.ofSubtypes subtypes
  let scope : ObjectExpr :=
    .inZones .battlefield (.all #[
      .any (subs.map fun s => .hasSubtype (.literal s)),
      .controlledBy .you
    ])
  mkAbility ({})
    (Instruction.grantKeywords scope #[Keyword.menace])
    s!"{joinedSubtypes subs CardSubtype.pluralName} you control gain menace until end of turn"

def exileThenReturnNextEnd : Effect :=
  mkAbility (.of .twoCreaturesOrLandsYouControl)
    (.moveZone .allTargets .exile .exile {
      delayedReturn? := some (.atNextEndStep false .owner)
    })
    "Exile up to two other target nonland permanents you control. Return those cards to the battlefield under their owner's control at the beginning of the next end step"

def searchBasicBeholdSubtypeUntap (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  mkAbility ({})
    (.bind ⟨0⟩ (.player (.searchLibrary {
        zones := .libraryOf .you
        filter := .all #[.hasSupertype .basic, .hasType .land]
        count := .upTo (.const 1)
        dest := .battlefield .controller
        mods := { tapped := true }
        reveal := false
        shuffle := true
      }))
      (Instruction.may .you (some (CostSpec.ofItem (.behold sub)))
        (Instruction.untap (.stepObjects ⟨0⟩))))
    s!"{capitalizeAscii (searchBasicLandTappedPhrase "your")}. You may behold {indefinite sub.englishName} {sub}. If you do, untap that land"

def searchBasicBeholdElfUntap : Effect :=
  searchBasicBeholdSubtypeUntap "Elf"

def twoPlayersDraw : Effect :=
  mkAbility (.of .twoPlayers)
    (.seq #[Instruction.drawFixed 1 (.target 0), Instruction.drawFixed 1 (.target 1)])
    "Two target players each draw a card"

def discardLegendarySameNameDraw : Effect :=
  mkAbility ({})
    (Instruction.drawFixed 2)
    "Draw two cards"

def dealDamageToAny (n : Nat) : Effect :=
  mkAbility (.of .anyTarget)
    (Instruction.dealDamageFixed (.targetSlot 0) n)
    s!"This creature deals {n} damage to any target"

def drawEqualSacrificedPowerThenDiscard : Effect :=
  mkAbility ({})
    (.seq #[
      Instruction.draw (.aggregate .sum (.stat .power) .costPaidObjects),
      Instruction.discardFixed 1
    ])
    "Draw cards equal to the sacrificed creature's power, then discard a card"

def arwenShare : Effect :=
  mkAbility (.of .anotherCreature)
    (.seq #[
      Instruction.grantKeywords (.target 0) #[Keyword.indestructible],
      Instruction.putPlusOne (.target 0) 1,
      Instruction.putCounters (.target 0) .lifelink,
      Instruction.putPlusOne .this 1,
      Instruction.putCounters .this .lifelink
    ])
    "Another target creature gains indestructible until end of turn. Put a +1/+1 counter and a lifelink counter on that creature and a +1/+1 counter and a lifelink counter on Arwen"

def grantCombatDamageCreateTreasure : Effect :=
  let trig : TriggeredAbility := {
    word := .whenever
    pattern := .thisDealsCombatDamageToPlayer
    effect := { body := Instruction.createTokensFixed .treasure 1 }
  }
  mkAbility (.of .creature)
    (.installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.grantTriggered #[trig])))
    "Until end of turn, target creature gains \"Whenever this creature deals combat damage to a player, create a Treasure token.\""

def putShadowCounter : Effect :=
  mkAbility (.of .creature)
    (.seq #[
      Instruction.putCounters (.target 0) .shadow,
      .installEffect (.applyContinuous (.whileHasCounter (.target 0) .shadow) (.target 0)
        (.modifyTypes { subtypes := #[.wraith] }))
    ])
    "Put a shadow counter on target creature. For as long as that creature has a shadow counter on it, it's a Wraith in addition to its other types"

def damageEachOpponent (n : Nat) : Effect :=
  mkAbility ({})
    (Instruction.dealDamageFixed (.players .opponents) n)
    s!"This deals {n} damage to each opponent"

def chooseTwoDestroyRest : Effect :=
  mkAbility (.of .none)
    (.moveZone allCreaturesExpr .graveyard .destroy {
      choice? := some {
        chooser := .controller
        count := .upTo (.const 2)
        invertSelection := true
      }
    })
    "Choose up to two creatures, then destroy the rest"

def blackGateUnblockable : Effect :=
  mkAbility (.of .creature)
    (.bind ⟨0⟩ (.player (.choose .you .playerWithMostLife))
      (.installEffect (.applyContinuous .untilEndOfTurn (.target 0)
        (.applyRule (.combat (.cantBeBlockedBy .self (.controlledBy (.ofExpr (.stepPlayers ⟨0⟩)))))))))
    "Choose a player with the most life or tied for most life. Target creature can't be blocked by creatures that player controls this turn"

def burdenThenDraw : Effect :=
  mkAbility ({})
    (.seq #[
      Instruction.putCounters .this .burden,
      Instruction.draw (.counterCount (some .burden) .this)
    ])
    "Put a burden counter on The One Ring, then draw a card for each burden counter on The One Ring"

def teamGain (k : Array KeywordAbility) : Effect :=
  mkAbility ({})
    (Instruction.grantKeywords creaturesYouControlExpr k)
    s!"Creatures you control gain {KeywordAbility.joinedAnd k} until end of turn"

def teamGainDoubleStrike : Effect :=
  teamGain #[Keyword.doubleStrike]

def sourceGainsIndestructibleTap : Effect :=
  mkAbility ({})
    (.seq #[
      Instruction.grantKeywords .this #[Keyword.indestructible],
      Instruction.tap .this
    ])
    "Witch-king of Angmar gains indestructible until end of turn. Tap him"

def plusOneOnEachOtherSubtype (subtype : String) (n : Nat) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  let scope : ObjectExpr :=
    .inZones .battlefield (.all #[.otherThan .this, .hasSubtype (.literal sub), .controlledBy .you])
  mkAbility ({})
    (Instruction.putPlusOne scope n)
    s!"Put {plusOnePlusOneCountersPhrase n} on each other {sub} you control"

def plusOneAndIndestructibleCounter : Effect :=
  mkAbility ({})
    (.seq #[
      Instruction.putPlusOne .this 1,
      Instruction.putCounters .this .indestructible
    ])
    "Put a +1/+1 counter and an indestructible counter on this"

def plusOneAndDraw (plus cards : Nat) : Effect :=
  mkAbility ({})
    (.seq #[Instruction.putPlusOne .this plus, Instruction.drawFixed cards])
    s!"Put {plusOnePlusOneCountersPhrase plus} on this and draw {cardPhrase cards}"

def plusOneAndExtraTurn : Effect :=
  mkAbility ({})
    (.seq #[
      Instruction.putPlusOne .this 1,
      .turn (.extraTurn .you (some (.player (.forbidAbilityActivation .any .powerUp))))
    ])
    "Put a +1/+1 counter on this. Take an extra turn after this one. During that turn, power-up abilities can't be activated"

def plusOneX : Effect :=
  mkAbility ({})
    (Instruction.putCounters .this .plusOnePlusOne .chosenX)
    "Put X +1/+1 counters on this"

def eachOppDiscardThenPlusOne : Effect :=
  mkAbility ({})
    (.seq #[
      .forEach (.eachPlayer .opponent) ⟨0⟩ (Instruction.discardFixed 1 (.stepPlayers ⟨0⟩)),
      Instruction.putPlusOne .this 1
    ])
    "Each opponent discards a card. Put a +1/+1 counter on this"

def lookAtTopPutTypes (n : Nat) (types : Array String) : Effect :=
  let subs := CardSubtype.ofSubtypes types
  let listed := orJoin types.toList
  let art := indefinite (types[0]?.getD "")
  mkAbility ({})
    (.seq #[
      Instruction.putPlusOne .this 2,
      .player (.inspectLibrary {
        source := .topCards .you (.const (Int.ofNat n)) false
        action := .takeMatching
          (.any (subs.map fun s => .hasSubtype (.literal s)))
          (.upTo (.const 1)) (.battlefield .controller) { mayTransformOnEnter := true }
        rest := .bottomRandom
      })
    ])
    s!"Put two +1/+1 counters on this, then look at the top {n} cards of your library. You may put {art} {listed} card from among them onto the battlefield. If it's a double-faced card, you may transform it. {restOnBottomRandomPhrase}"

def lookAtTopPutHeroEquipVehicle (n : Nat) : Effect :=
  lookAtTopPutTypes n #["Hero", "Equipment", "Vehicle"]

def transform : Effect :=
  mkAbility ({})
    (.permanent (.transform .this))
    "Transform this"

def drawX : Effect :=
  mkAbility ({})
    (Instruction.draw .chosenX)
    "Draw X cards"

def lookAtTopRevealArtifact (n : Nat) : Effect :=
  mkAbility ({})
    (.player (.inspectLibrary {
      source := .topCards .you (.const (Int.ofNat n)) false
      action := .takeMatching (.hasType .artifact) (.upTo (.const 1)) (.hand .controller) {} true
      rest := .bottomRandom
    }))
    s!"Look at the top {n} cards of your library. You may reveal an artifact card from among them and put it into your hand. {restOnBottomRandomPhrase}"

def connive : Effect :=
  mkAbility ({})
    (.player (.connive .this))
    "This creature connives"

def addAnyColorSpendOnlySubtype (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  mkAbility ({})
    (Instruction.addMana {
      spec := .oneOf .anyColor (.const 1)
      restriction := some (.subtypeSpellOrSource sub)
    })
    s!"Add one mana of any color. Spend this mana only to cast {indefinite sub.englishName} {sub} spell or to activate an ability of {indefinite sub.englishName} {sub} source"

def addAnyColorSpendOnlyHero : Effect :=
  addAnyColorSpendOnlySubtype "Hero"

def addAnyColorSpendOnlyVillain : Effect :=
  addAnyColorSpendOnlySubtype "Villain"

def addAnyColorSpendOnlyArtifactSpell : Effect :=
  mkAbility ({})
    (Instruction.addMana {
      spec := .oneOf .anyColor (.const 1)
      restriction := some (.onlyForSpells (.hasType .artifact))
    })
    "Add one mana of any color. Spend this mana only to cast an artifact spell"

def addTwoAnyColorCreatureSources : Effect :=
  mkAbility ({})
    (Instruction.addMana {
      spec := .oneOf .anyColor (.const 2)
      restriction := some (.onlyForAbilities (.sourceMatches (.hasType .creature)))
    })
    "Add two mana of any one color. Spend this mana only to activate abilities of creature sources"

def addBlueCantNonartifact : Effect :=
  mkAbility ({})
    (Instruction.addMana {
      spec := .fixedOne (.colored .blue)
      restriction := some (.cantSpendOnSpells (.not (.hasType .artifact)))
    })
    "Add {U}. This mana can't be spent to cast a nonartifact spell"

def addAnyColorEqualToSourcePower : Effect :=
  mkAbility ({})
    (Instruction.addMana {
      spec := .oneOf .anyColor (.objectStat .power .this)
    })
    "Add X mana of any one color, where X is this creature's power"

def addFourAnyCombination : Effect :=
  mkAbility ({})
    (Instruction.addMana { spec := .combination .anyColor (.const 4) })
    "Add four mana in any combination of colors"

def addTwoAnyColorEquipment : Effect :=
  mkAbility ({})
    (Instruction.addMana {
      spec := .oneOf .anyColor (.const 2)
      restriction := some (.onlyForSpellsOrAbilities (.hasSubtype .equipment) .equip)
    })
    "Add two mana of any one color. Spend this mana only to cast Equipment spells or activate equip abilities"

def drawPerDiscardedThisTurn : Effect :=
  mkAbility ({})
    (Instruction.draw (.playerMetric .cardsDiscardedThisTurn .you))
    "Draw a card for each card you've discarded this turn"

def createTokensEqualRemovedPlusOnes (kind : TokenSpec) : Effect :=
  mkAbility ({})
    (Instruction.createTokens kind .eventAmount)
    s!"Create that many {kind.pluralNoun}"

def exileTopXPlayThisTurn : Effect :=
  mkAbility ({})
    (.moveZone (.topOfLibrary .you (.objectStat .power .this)) .exile .exile {
      grantPlayPerm? := some { duration := .untilEndOfTurn, landsAllowed := true }
    })
    "Exile the top X cards of your library, where X is this creature's power. You may play those cards this turn"

def copyControlledAbility (ty : CardType) : Effect :=
  let w := ty.oracleWord
  mkAbility (.of (.stackAbilityFromSource ty))
    (.stack (.copyStackObject (.target 0) (.const 1) true))
    s!"Copy target activated or triggered ability you control from {indefinite w} {w} source. You may choose new targets for the copy"

def createTokensEqualSubtype (kind : TokenSpec) (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  let cnt : ValueExpr :=
    .aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal sub), .controlledBy .you]))
  mkAbility ({})
    (Instruction.createTokens kind cnt)
    s!"Create X {kind.pluralNoun}, where X is the number of {sub}s you control"

def createTappedTokens (kind : TokenSpec) (n : Nat) : Effect :=
  mkAbility ({})
    (Instruction.createTokensFixed kind n .you true)
    (capitalizeAscii (TokenSpec.createPhrase kind n (tapped := true)))

def destroyUpToOneThenPlusOne : Effect :=
  mkAbility (.of .artifactOrEnchantment)
    (.seq #[Instruction.destroy (.target 0), Instruction.putPlusOne .this 1])
    "Destroy up to one target artifact or enchantment. Put a +1/+1 counter on this"
    (allowsZeroTargets := true)

def proliferateEachKind : Effect :=
  mkAbility (.of .permanentOrPlayer)
    (.player (.proliferate .you (.const 1) (some (.target 0))))
    "For each kind of counter on target permanent or player, give that permanent or player another counter of that kind"

def equipmentBecomesConstructHero : Effect :=
  let artifactsCount : ValueExpr :=
    .aggregate .count .one (.inZones .battlefield (.all #[.hasType .artifact, .controlledBy .you]))
  mkAbility ({})
    (Instruction.ifThen (.exists (.filter .this (.not (.hasType .creature))))
      (.installEffect (.applyContinuous .untilEndOfTurn .this
        (.all #[
          .modifyTypes { mode := .setAndKeepNoncreatureSubtypes, types := #[.artifact, .creature], subtypes := #[.construct, .hero] },
          .setBasePT (some (.const 0)) (some (.const 0)),
          .grantKeywords #[Keyword.flying],
          .modifyPT artifactsCount artifactsCount
        ]))))
    "If this Equipment isn't a creature, it becomes a 0/0 Construct Hero artifact creature with flying and \"This creature gets +1/+1 for each artifact you control\" until end of turn"

def lookAtTopRevealSubtype (n : Nat) (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  mkAbility ({})
    (.player (.inspectLibrary {
      source := .topCards .you (.const (Int.ofNat n)) false
      action := .takeMatching (.hasSubtype (.literal sub)) (.upTo (.const 1)) (.hand .controller) {} true
      rest := .bottomAnyOrder
    }))
    s!"Look at the top {n} cards of your library. You may reveal a {sub} card from among them and put it into your hand. Put the rest on the bottom of your library in any order"

def millThenPutSubtypeOrEnchantment (n : Nat) (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  mkAbility ({})
    (.player (.inspectLibrary {
      source := .millCards .you (.const (Int.ofNat n))
      action := .takeMatching (.any #[.hasSubtype (.literal sub), .hasType .enchantment])
        (.upTo (.const 1)) (.hand .controller)
      rest := .leaveInPlace
    }))
    s!"Mill {n} cards. You may put {indefinite sub.englishName} {sub} or enchantment card from among those cards into your hand"

def millThenPutHeroOrEnchantment (n : Nat) : Effect :=
  millThenPutSubtypeOrEnchantment n "Hero"

def plusOneAndDoubleStrikeCounter : Effect :=
  mkAbility ({})
    (.seq #[Instruction.putPlusOne .this 1, Instruction.putCounters .this .doubleStrike])
    "Put a +1/+1 counter and a double strike counter on this"

def plusOneThenFightUpToOne : Effect :=
  mkAbility (.of .oppCreature)
    (.seq #[
      Instruction.putPlusOne .this 1,
      .damage (.fight .this (.target 0) false)
    ])
    "Put a +1/+1 counter on this. This fights up to one target creature an opponent controls"
    (allowsZeroTargets := true)

def plusOneAndGrant (k : Array KeywordAbility) : Effect :=
  let joined :=
    if KeywordAbility.hasVigilance k && KeywordAbility.hasIndestructible k && KeywordAbility.hasHaste k then
      "vigilance, indestructible, and haste"
    else KeywordAbility.joinedAnd k
  mkAbility ({})
    (.seq #[Instruction.putPlusOne .this 1, Instruction.grantKeywords .this k])
    s!"Put a +1/+1 counter on this. He gains {joined} until end of turn"

def plusOneAndCreateTigerGod : Effect :=
  mkAbility ({})
    (.seq #[Instruction.putPlusOne .this 1, Instruction.createTokensFixed .tigerGod 1])
    "Put a +1/+1 counter on this and create The Tiger God, a legendary 4/4 green Cat God creature token with \"The Tiger God can't be blocked by more than one creature.\""

def plusOneAndCreateTokens (n : Nat) (kind : TokenSpec) : Effect :=
  mkAbility ({})
    (.seq #[Instruction.putPlusOne .this n, Instruction.createTokensFixed kind 1])
    s!"Put {plusOnePlusOneCountersPhrase n} on this creature and {TokenSpec.createPhrase kind 1}"

def plusTwoThenOddEvenDestroy : Effect :=
  mkAbility ({})
    (.seq #[
      Instruction.putPlusOne .this 2,
      .bind ⟨0⟩ (.player (.choose .you .oddOrEven))
        (Instruction.destroy (.inZones .battlefield (.all #[
          .hasType .creature, .otherThan .this, .statParity .manaValue (.fromStep ⟨0⟩)
        ])))
    ])
    "Put two +1/+1 counters on this. Choose odd or even. Destroy each other creature with mana value of the chosen quality"

def returnFromGyFinalityAttach : Effect :=
  let equipYouControl : ObjectExpr :=
    .inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .controlledBy .you])
  mkAbility ({})
    (.bind ⟨0⟩ (.moveZone .this (.battlefield .controller) .put {
        enterCounters := #[(.finality, .const 1)]
      })
      (Instruction.may .you none (.permanent (.attach equipYouControl (.stepObjects ⟨0⟩) true))))
    "Return this card from your graveyard to the battlefield with a finality counter on him. Then you may attach an Equipment you control to him"

def returnGyCreatureThenPlusOne (n : Nat) : Effect :=
  mkAbility (.of .creatureCardInYourGraveyard)
    (.seq #[
      .moveZone (.target 0) (.hand .controller) .returnToHand {},
      Instruction.putPlusOne .this n
    ])
    s!"Return up to one target creature card from your graveyard to your hand. Put {plusOnePlusOneCountersPhrase n} on this creature"
    (allowsZeroTargets := true)

def revealTopDrawIfArtifact : Effect :=
  mkAbility ({})
    (.bind ⟨0⟩ (.player (.reveal .you (.topOfLibrary .you (.const 1))))
      (Instruction.ifThen (.exists (.filter (.stepObjects ⟨0⟩) (.hasType .artifact)))
        (Instruction.drawFixed 1)))
    "Reveal the top card of your library. If it's an artifact card, draw a card"

def copyArtifactYouControlNotLegendary : Effect :=
  mkAbility (.of .twoArtifactsYouControl)
    (.installEffect (.applyContinuous .untilEndOfTurn (.target 0)
      (.becomeCopyOf (.target 1) #[.removeSupertype .legendary])))
    "Target artifact you control becomes a copy of a second target artifact you control until end of turn, except it isn't legendary"

def pumpAttackingAloneGainLife : Effect :=
  mkAbility (.of .attackingAloneCreatureYouControl)
    (.seq #[Instruction.pumpFixed (.target 0) 1 0, Instruction.gainLifeFixed 1])
    "Target attacking creature you control gets +1/+0 until end of turn. You gain 1 life"

def becomeTypes (types : Array String) (power toughness : Int) (k : Array KeywordAbility) : Effect :=
  let subs := CardSubtype.ofSubtypes types
  let joined :=
    if KeywordAbility.hasReach k && KeywordAbility.hasVigilance k then "reach and vigilance"
    else KeywordAbility.joinedAnd k
  let names := (subs.map CardSubtype.englishName).toList
  let typeWords := String.intercalate " " names
  let art := indefinite (names[0]?.getD "")
  mkAbility ({})
    (.installEffect (.applyContinuous .untilEndOfTurn .this
      (.all #[
        .modifyTypes { mode := .setAndKeepNoncreatureSubtypes, types := #[.creature], subtypes := subs },
        .setBasePT (some (.const power)) (some (.const toughness)),
        .grantKeywords k
      ])))
    s!"Until end of turn, this becomes {art} {typeWords} with base power and toughness {power}/{toughness} and gains {joined}"

def becomeDinosaurHero (power toughness : Int) (k : Array KeywordAbility) : Effect :=
  becomeTypes #["Dinosaur", "Hero"] power toughness k

def nextInstantSorceryCopyIfMvAtMostSourcePower : Effect :=
  mkAbility ({})
    (.installEffect (.createDelayedTrigger {
      pattern := .castSpell .you (.all #[
        .any #[.hasType .instant, .hasType .sorcery],
        .stat .manaValue .le (.objectStat .power .this)
      ])
      duration := .untilEndOfTurn
      oneShot := true
      effect := { body := .stack (.copyStackObject .triggerSubject (.const 1) true) }
    }))
    "When you next cast an instant or sorcery spell with mana value less than or equal to this creature's power this turn, copy that spell. You may choose new targets for the copy"

def harnessInfinityStone : Effect :=
  mkAbility ({})
    (.permanent (.setDesignation .this .harnessed true))
    "Harness this"

def destroyTargetNoncreatureArtOrEnch : Effect :=
  destroyTarget .noncreatureArtifactOrEnchantment (capitalize := true)

def targetSubtypeConnives (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  mkAbility (.of (.creatureYouControlSubtype sub))
    (.player (.connive (.target 0)))
    s!"Target {sub} you control connives"

def anotherYouControlGetsAndGrant (p t : Int) (k : Array KeywordAbility) : Effect :=
  mkAbility (.of .anotherCreatureYouControl)
    (.seq #[
      Instruction.pumpFixed (.target 0) p t,
      Instruction.grantKeywords (.target 0) k
    ])
    s!"Another target creature you control gets {signedStat p}/{signedStat t} and gains {KeywordAbility.joinedAnd k} until end of turn"

def tapTargetCreature : Effect :=
  mkAbility (.of .creature)
    (Instruction.tap (.target 0))
    "Tap target creature"

def targetGets (p t : Int) : Effect :=
  mkAbility (.of .creature)
    (Instruction.pumpFixed (.target 0) p t)
    s!"Target creature gets {signedStat p}/{signedStat t} until end of turn"

/-! ### Ability-Phrased Factories for Names That Overlap Spells -/

def abilityCreateTokens (kind : TokenSpec) (n : Nat) : Effect :=
  mkAbility ({})
    (Instruction.createTokensFixed kind n)
    (capitalizeAscii (TokenSpec.createPhrase kind n))

def abilityCreateTokensX (kind : TokenSpec) : Effect :=
  mkAbility ({})
    (Instruction.createTokens kind .chosenX)
    s!"Create X {kind.pluralNoun}"

def abilityCreaturesYouControlGet (power toughness : Int) : Effect :=
  mkAbility ({})
    (Instruction.pumpFixed creaturesYouControlExpr power toughness)
    s!"Creatures you control get {signedStat power}/{signedStat toughness} until end of turn"

def abilityDealDamageToEachCreature (n : Nat) : Effect :=
  mkAbility ({})
    (Instruction.dealDamageFixed (.objects allCreaturesExpr) n)
    s!"This deals {n} damage to each creature"

def abilityDraw (n : Nat) : Effect :=
  mkAbility ({})
    (Instruction.drawFixed n)
    s!"Draw {cardPhrase n}"

def abilityDrawThenDiscard (n : Nat) : Effect :=
  mkAbility ({})
    (.seq #[Instruction.drawFixed n, Instruction.discardFixed 1])
    s!"Draw {cardPhrase n}, then discard a card"

def abilityScry (n : Nat) : Effect :=
  mkAbility ({})
    (Instruction.scryFixed n)
    s!"Scry {n}"

def abilityTargetPlayerDraw (n : Nat) : Effect :=
  mkAbility (.of .player)
    (Instruction.drawFixed n (.target 0))
    s!"target player draws {cardPhrase n}"

/-! ### Reality Fracture Ability & Spell Effects -/

def abilityEmpowerJace (n : Nat) : Effect :=
  mkAbility ({})
    (Instruction.empowerJace n)
    s!"Empower Jace {n}"

def abilitySurveil (n : Nat) : Effect :=
  mkAbility ({})
    (Instruction.surveilFixed n)
    s!"Surveil {n}"

def targetCreatureBecomesPrepared : Effect :=
  mkAbility (.of .creature)
    (Instruction.becomePrepared (.target 0))
    "Target creature becomes prepared"

def eachCreatureYouControlBecomesPrepared : Effect :=
  mkAbility ({})
    (Instruction.becomePrepared creaturesYouControlExpr)
    "Each creature you control becomes prepared"

def plusOneThenGainLife (n life : Nat) : Effect :=
  mkAbility (.of .creature)
    (.seq #[Instruction.putPlusOne (.target 0) n, Instruction.gainLifeFixed life])
    s!"Put {plusOnePlusOneCountersPhrase n} on target creature. You gain {life} life"

def damageTargetOpponent (n : Nat) : Effect :=
  mkAbility (.of .opponent)
    (Instruction.dealDamageFixed (.targetSlot 0) n)
    s!"This deals {n} damage to target opponent"

def millSelf (n : Nat) : Effect :=
  mkAbility ({})
    (Instruction.millFixed n)
    s!"Mill {cardPhrase n}"

def mayDiscardDraw (n : Nat) : Effect :=
  mkAbility ({})
    (Instruction.may .you (some (CostSpec.ofItem (.discard (.count (.const 1)) (.matching .anyObject))))
      (Instruction.drawFixed n))
    s!"You may discard a card. If you do, draw {cardPhrase n}"

def createTokensThenSurveil (kind : TokenSpec) (n s : Nat) : Effect :=
  mkAbility ({})
    (.seq #[Instruction.createTokensFixed kind n, Instruction.surveilFixed s])
    s!"{capitalizeAscii (TokenSpec.createPhrase kind n)}. Surveil {s}"

def createTokensLifeGained (kind : TokenSpec) : Effect :=
  mkAbility ({})
    (Instruction.createTokens kind (.playerMetric .lifeGainedThisTurn .you))
    s!"Create X {kind.pluralNoun}, where X is the amount of life you gained this turn"

def setBasePT (power toughness : Int) : Effect :=
  mkAbility (.of .creature)
    (Instruction.setBasePTFixed (.target 0) power toughness)
    s!"Target creature has base power and toughness {power}/{toughness} until end of turn"

def oppSacrificesGreatestMvGainLife (life : Nat) : Effect :=
  let oppCreaturesOrWalkers : ObjectExpr :=
    .inZones .battlefield (.all #[
      .any #[.hasType .creature, .hasType .planeswalker],
      .controlledBy (.ofExpr (.target 0))
    ])
  mkAbility (.of .opponent)
    (.seq #[
      .moveZone oppCreaturesOrWalkers .graveyard .sacrifice {
        choice? := some {
          chooser := .player (.target 0)
          count := .exact (.const 1)
          extremeMetric? := some (true, .stat .manaValue)
        }
      },
      Instruction.gainLifeFixed life
    ])
    s!"Target opponent sacrifices a creature or planeswalker with the greatest mana value among creatures and planeswalkers they control. You gain {life} life"

def damageThenEmpowerExcess (n : Nat) : Effect :=
  mkAbility (.of .creatureOrPlaneswalker)
    (.bind ⟨0⟩ (.damage (.deal .this (.targetSlot 0) (.const (Int.ofNat n)) { trackExcess := true }))
      (Instruction.ifThen (.cmp .gt (.stepMetric .excessDamage ⟨0⟩) (.const 0))
        (Instruction.empower .jace (.stepMetric .excessDamage ⟨0⟩))))
    s!"This deals {n} damage to target creature or planeswalker. If excess damage was dealt to that permanent this way, empower Jace X, where X is that excess damage"

def jaceLoyaltyAtInstantSpeed : Effect :=
  mkAbility ({})
    (.installEffect (.applyRule .untilEndOfTurn
      (.play (.activateLoyaltyAsInstant .you (.hasSubtype (.literal .jace))))))
    "Until end of turn, you may activate loyalty abilities of Jace planeswalkers you control on any player's turn any time you could cast an instant"

def exileTopMayCastElseDamageOpponents (n : Nat) : Effect :=
  mkAbility ({})
    (.bind ⟨0⟩ (.moveZone (.topOfLibrary .you (.const 1)) .exile .exile {})
      (.bind ⟨1⟩ (.stack (.mayCastOrPlay (.stepObjects ⟨0⟩) {
          duration := .untilEndOfTurn
          landsAllowed := false
        }))
        (Instruction.ifThen (.not (.stepSucceeded ⟨1⟩))
          (Instruction.dealDamageFixed (.players .opponents) n))))
    s!"Exile the top card of your library. You may cast that card. If you don't, this deals {n} damage to each opponent"

def emblemCastSpellDamage (n : Nat) : Effect :=
  mkAbility ({})
    (.create (.emblem .you {
      triggeredAbilities := #[{
        word := .whenever
        pattern := .castSpell .you .anyObject
        effect := {
          targeting := .of .anyTarget
          body := Instruction.dealDamageFixed (.targetSlot 0) n
          phrase := s!"this emblem deals {n} damage to any target"
        }
      }]
    }))
    s!"You get an emblem with \"Whenever you cast a spell, this emblem deals {n} damage to any target.\""

def returnFromGyWithFinality : Effect :=
  mkAbility ({})
    (.moveZone .this (.battlefield .controller) .put {
      enterCounters := #[(.finality, .const 1)]
    })
    "Return this card from your graveyard to the battlefield with a finality counter on it"

def firstDealsStatDamageToSecond (useLoyalty : Bool) : Effect :=
  let spec : TargetSpec :=
    if useLoyalty then .planeswalkerYouControlThenOppCreatureOrPlaneswalker
    else .creatureYouControlThenOppCreatureOrPlaneswalker
  let stat : StatKind := if useLoyalty then .loyalty else .power
  let phrase :=
    if useLoyalty then
      "Target planeswalker you control deals damage equal to its loyalty to target creature or planeswalker an opponent controls"
    else
      "Target creature you control deals damage equal to its power to target creature or planeswalker an opponent controls"
  mkAbility (.of spec)
    (Instruction.dealDamage (.targetSlot 1) (.objectStat stat (.target 0)) (.target 0))
    phrase

def tapAndStunTargetCreature : Effect :=
  mkAbility (.of .creature)
    (Instruction.tapAndStun (.target 0))
    "Tap target creature and put a stun counter on it"

def copyNextInstantSorceryThisTurn : Effect :=
  mkAbility ({})
    (.installEffect (.createDelayedTrigger {
      pattern := .castSpell .you (.any #[.hasType .instant, .hasType .sorcery])
      duration := .untilEndOfTurn
      oneShot := true
      effect := { body := .stack (.copyStackObject .triggerSubject (.const 1) true) }
    }))
    "When you next cast an instant or sorcery spell this turn, copy that spell. You may choose new targets for the copy"

def proliferatePlaneswalkerTypesTimes : Effect :=
  let pwTypesCount : ValueExpr :=
    .subtypeCount .planeswalker (.inZones .battlefield (.all #[.hasType .planeswalker, .controlledBy .you]))
  mkAbility ({})
    (.player (.proliferate .you pwTypesCount none))
    "Proliferate X times, where X is the number of planeswalker types among planeswalkers you control"

def copyEachCreatureOfTargetPlayer : Effect :=
  let targetPlayerCreatures : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .controlledBy (.ofExpr (.target 0))])
  let sacEndStep : GrantedAbility :=
    .triggered {
      word := .at
      pattern := .stepEachEndStep
      interveningIf? := some (.not (.exists (.inZones .battlefield (.all #[
        .hasType .planeswalker, .controlledBy .you
      ]))))
      effect := { body := Instruction.sacrifice .this }
    }
  mkAbility (.of .player)
    (.forEach (.eachObject targetPlayerCreatures) ⟨0⟩
      (Instruction.createTokens (.copyOf (.stepObjects ⟨0⟩) #[
        .addKeywords #[Keyword.haste],
        .addAbilities #[sacEndStep]
      ])))
    "For each creature target player controls, create a token that's a copy of that creature, except it has haste and \"At the beginning of the end step, if you don't control a planeswalker, sacrifice this creature.\""

def cantBeBlockedAnotherPowerAtMost (n : Int) : Effect :=
  let spec := TargetSpec.anotherCreatureYouControlPowerAtMost n
  mkAbility (.of spec)
    (Instruction.cantBeBlocked (.target 0))
    s!"{capitalizeAscii spec.noun} can't be blocked this turn"

/-- The printed “put N +1/+1 counters on” effect for `spec`.
`creature` is the pump spell; a creature you control, including a subtype
list, is the activated ability. -/
def canonicalPlusOne (n : Nat) (spec : TargetSpec) : Option Effect :=
  if spec == .creature then
    some (mkSpell (.of .creature) (Instruction.putPlusOne (.target 0) n)
      s!"put {plusOnePlusOneCountersPhrase n} on target creature")
  else if spec == .creatureYouControl then
    some (plusOneOnTarget n)
  else match spec.creatureYouControlAnySubtype? with
    | some ss =>
      some (if ss.isEmpty then plusOneOnTarget n else plusOneOnTarget n (ss.map CardSubtype.englishName))
    | none => none

def becomeCopyLegendRuleOff : Effect :=
  mkAbility (.of .creatureYouControl)
    (.seq #[
      .installEffect (.applyContinuous .untilEndOfTurn .this (.becomeCopyOf (.target 0) #[])),
      .installEffect (.applyRule .untilEndOfTurn (.game (.legendRuleDisabled .you)))
    ])
    "This land becomes a copy of target creature you control until end of turn. The \"legend rule\" doesn't apply to permanents you control this turn"

/-! ### Reality Fracture Named Spell Effects (Unified `Instruction`) -/

/-- A spell effect with its printed wording. -/
def fraSpell (spec : TargetSpec) (body : Instruction) (phrase : String)
    (maxTargets : Nat := 0) (allowsZeroTargets := false) : Effect :=
  { targeting := .of spec, body, phrase, maxTargets, allowsZeroTargets }

def fraSpellOn (d : TargetDomain) (body : Instruction) (phrase : String) : Effect :=
  fraSpell (.ofDomain d) body phrase

def fraUntargeted (body : Instruction) (phrase : String) : Effect :=
  fraSpell .none body phrase

/-! ## White -/

def generousRevival : Effect :=
  fraSpell (.creatureCardInYourGraveyardMvAtMost 3)
    (.moveZone (.target 0) (.battlefield .controller) .put {
      enterCounters := #[(.plusOnePlusOne, .const 1)]
    })
    "Return target creature card with mana value 3 or less from your graveyard to the battlefield with an additional +1/+1 counter on it"

def hexhavenBattalion : Effect :=
  fraUntargeted (Instruction.createTokensFixed .cadet 3)
    "Create three 2/2 colorless Wizard Soldier creature tokens named Cadet"

def kindredJudgment : Effect :=
  fraUntargeted
    (.bind ⟨0⟩ (.player (.choose .you .creatureType))
      (Instruction.destroy (.inZones .battlefield (.all #[
        .hasType .creature, .not (.hasSubtype (.fromStep ⟨0⟩))
      ]))))
    "Choose a creature type. Destroy all creatures that aren't of the chosen type"

def loyalTutor : Effect :=
  fraUntargeted
    (.player (.searchLibrary {
      zones := .libraryOf .you
      filter := .hasType .planeswalker
      count := .upTo (.const 1)
      dest := .library .owner .top false
      reveal := true
      shuffle := true
    }))
    "Search your library for a planeswalker card, reveal it, then shuffle and put that card on top"

def predictivePreparations : Effect :=
  fraSpell (.single { domain := .creature, count := .between 1 2 })
    (Instruction.putPlusOne .allTargets 1)
    "Put a +1/+1 counter on each of one or two target creatures"
    (maxTargets := 2)

def prophesiedEnd : Effect :=
  fraSpell .creature
    (.bind ⟨0⟩ (Instruction.destroy (.target 0))
      (Instruction.ifThen (.exists (.filter (.target 0) (.not (.combatRole .attacking))))
        (Instruction.drawFixed 1 (.controllerOf (.target 0)))))
    "Destroy target creature. If it wasn't attacking, its controller draws a card"

def refuteDestiny : Effect :=
  fraSpellOn (.object .battlefield (.all #[
      .any #[.hasType .creature, .hasType .planeswalker],
      .any #[.hasColor (.literal .green), .hasColor (.literal .blue)]]))
    (.seq #[Instruction.exile (.target 0), Instruction.surveilFixed 1])
    "Exile target creature or planeswalker that's green or blue. Surveil 1"

def returnToTheLightRealms : Effect :=
  fraUntargeted
    (.moveZone (.inZones (.graveyardOf .you) (.all #[.isKind .permanentCard, .not (.hasType .land)]))
      (.battlefield .controller) .put {})
    "Return all nonland permanent cards from your graveyard to the battlefield"

def surgicalPrecisionDestroy : Effect :=
  fraSpell (.creatureToughnessAtLeast 4)
    (.seq #[Instruction.destroy (.target 0), Instruction.gainLifeFixed 1])
    "Destroy target creature with toughness 4 or greater. You gain 1 life"

def drawAndGainLife (cards life : Nat) : Effect :=
  fraUntargeted
    (.seq #[Instruction.drawFixed cards, Instruction.gainLifeFixed life])
    s!"You draw {cardPhrase cards} and gain {life} life"

def yourFateEndsHere : Effect :=
  fraSpellOn (.object .battlefield (.all #[
      .any #[.hasType .creature, .hasType .planeswalker],
      .stat .manaValue .ge (.const 3)]))
    (.seq #[Instruction.destroy (.target 0), Instruction.surveilFixed 1])
    "Destroy target creature or planeswalker with mana value 3 or greater. Surveil 1"

/-! ## Blue -/

def counterTargetSpell : Effect :=
  fraSpell .spell (Instruction.counter (.target 0)) "Counter target spell"

def cruelCalculations : Effect :=
  fraSpell .player
    (Instruction.draw (.playerMetric .cardsMilledThisTurn (.target 0)))
    "Draw X cards, where X is the number of cards that were put into target player's graveyard from their library this turn"

def icyReceptionCounter : Effect :=
  fraSpellOn (.object .stack (.all #[
      .any #[.hasType .creature, .hasSupertype .legendary],
      .isKind .spell]))
    (.unlessPays (.controllerOf (.target 0)) (CostSpec.ofGeneric 3) (Instruction.counter (.target 0)))
    "Counter target creature or legendary spell unless its controller pays {3}"

def targetCreatureGets (p t : Int) : Effect :=
  fraSpell .creature (Instruction.pumpFixed (.target 0) p t)
    s!"Target creature gets {signedStat p}/{signedStat t} until end of turn"

def preciseRedaction : Effect :=
  fraSpellOn (.object .stack (.all #[
      .any #[.hasColor (.literal .white), .hasColor (.literal .black)],
      .isKind .spell]))
    (Instruction.counter (.target 0))
    "Counter target white or black spell"

def sphinxsApproach : Effect :=
  fraUntargeted
    (.seq #[
      Instruction.drawFixed 2,
      Instruction.may .you
        (some (CostSpec.ofItems #[
          .exile (.count (.const 1)) .stack .self,
          .exile (.count (.const 4)) .yourGraveyard (.filter (.named (.literal "Sphinx's Approach")))
        ]))
        (.player (.searchLibrary {
          zones := .libraryOf .you
          filter := .all #[.hasType .creature, .hasSubtype (.literal .sphinx)]
          count := .upTo (.const 1)
          dest := .battlefield .controller
          reveal := false
          shuffle := true
        }))
    ])
    "Draw two cards. Then you may exile this spell and four cards named Sphinx's Approach from your graveyard. If you do, search your library for a Sphinx creature card, put it onto the battlefield, then shuffle"

def unsummon : Effect :=
  fraSpell .creature (Instruction.bounce (.target 0))
    "Return target creature to its owner's hand"

def unwindHistory : Effect :=
  fraSpellOn (.object .battlefield (.all #[
      .hasType .creature, .controlledBy .opponent, .stat .manaValue .le (.const 3)]))
    (.seq #[Instruction.bounce (.target 0), Instruction.surveilFixed 1])
    "Return target creature an opponent controls with mana value 3 or less to its owner's hand. Surveil 1"

def arcOfFortune : Effect :=
  fraUntargeted
    (.forEach (.eachPlayer .any) ⟨0⟩
      (Instruction.may (.stepPlayers ⟨0⟩) none
        (.seq #[
          .moveZone (.inZones (.handOf (.stepPlayers ⟨0⟩)) .anyObject) .graveyard .discard {},
          Instruction.drawFixed 7 (.stepPlayers ⟨0⟩)
        ])))
    "Each player may discard their hand and draw seven cards"

/-! ## Black -/

def castAwayDoubt : Effect :=
  fraUntargeted
    (.seq #[Instruction.drawFixed 2, Instruction.dealDamageFixed (.players .eachPlayer) 2])
    "Draw two cards. This spell deals 2 damage to each player"

def extendedAbsence : Effect :=
  fraSpell .creatureOrPlaneswalker
    (.seq #[
      Instruction.exile (.target 0),
      Instruction.dealDamageFixed (.players .opponents) 1,
      Instruction.gainLifeFixed 1
    ])
    "Exile target creature or planeswalker. This spell deals 1 damage to each opponent and you gain 1 life"

def extrapolateTheImpossible : Effect :=
  fraUntargeted
    (Instruction.may .you none
      (.player (.inspectLibrary {
        source := .outsideTheGame .you 2
        action := .takeMatching .anyObject (.exact (.const 1)) (.hand .controller)
        rest := .leaveInPlace
        chooser := .opponents
      })))
    "You may reveal exactly two cards you own with different names from outside the game. An opponent chooses one of them. You put that card into your hand"

def overwriteTheMultiverse : Effect :=
  fraUntargeted
    (.bind ⟨0⟩ (Instruction.exile allCreaturesExpr)
      (Instruction.empower .jace (.stepMetric .movedCount ⟨0⟩)))
    "Exile all creatures. Empower Jace X, where X is the number of creatures exiled this way"

def rewriteRegrets : Effect :=
  fraSpellOn (.object .yourGraveyard (.all #[
      .any #[.hasType .creature, .hasType .planeswalker],
      .isKind .card,
      .stat .manaValue .le (.const 6)]))
    (.moveZone (.target 0) (.battlefield .controller) .put {})
    "Return target creature or planeswalker card with mana value 6 or less from your graveyard to the battlefield"

def riseDraw : Effect :=
  fraUntargeted
    (.bind ⟨0⟩ (Instruction.draw (.aggregate .max (.stat .power) creaturesYouControlExpr))
      (Instruction.loseLife (.stepMetric .movedCount ⟨0⟩)))
    "Draw cards equal to the greatest power among creatures you control. You lose life equal to the number of cards drawn this way"

def destroyTargetCreatureOrPlaneswalker : Effect :=
  fraSpell .creatureOrPlaneswalker (Instruction.destroy (.target 0))
    "Destroy target creature or planeswalker"

def solveForDisappointment : Effect :=
  fraSpell .opponent
    (.moveZone (.inZones (.handOf (.target 0)) (.all #[.isKind .permanentCard, .not (.hasType .land)]))
      .graveyard .discard {
        choice? := some { chooser := .controller, count := .exact (.const 1), revealFirst := true }
      })
    "Target opponent reveals their hand. You choose a nonland permanent card from it. That player discards that card"

def terminalCriticism : Effect :=
  fraSpellOn (.object .battlefield (.all #[
      .any #[.hasType .creature, .hasType .planeswalker],
      .any #[.hasColor (.literal .blue), .hasColor (.literal .red)]]))
    (.seq #[Instruction.destroy (.target 0), Instruction.gainLifeFixed 1])
    "Destroy target creature or planeswalker that's blue or red. You gain 1 life"

def vraskasMercyDestroy : Effect :=
  fraSpell .creatureOrPlaneswalker
    (.seq #[Instruction.loseLifeFixed 2, Instruction.destroy (.target 0)])
    "You lose 2 life. Destroy target creature or planeswalker"

def vraskasMercyEmpower : Effect :=
  fraUntargeted
    (.seq #[Instruction.loseLifeFixed 2, Instruction.empowerJace 6])
    "You lose 2 life. Empower Jace 6"

/-! ## Red -/

def artifistAcumen : Effect :=
  fraUntargeted
    (.seq #[
      Instruction.grantKeywords creaturesYouControlExpr #[Keyword.firstStrike],
      Instruction.drawFixed 1
    ])
    "Creatures you control gain first strike until end of turn.\nDraw a card"

def awakenTheInferno : Effect :=
  fraSpell (.ofSlots #[.of .oppCreatureOrPlaneswalker, { domain := .creatureYouControl, count := .upTo 1 }])
    (.seq #[
      Instruction.dealDamageFixed (.targetSlot 0) 6,
      Instruction.putPlusOne (.target 1) 1
    ])
    "This spell deals 6 damage to target creature or planeswalker an opponent controls. Put a +1/+1 counter on up to one target creature you control"

def commandTheStage : Effect :=
  let wizardTokens : ObjectExpr :=
    .inZones .battlefield (.all #[.isToken true, .hasSubtype (.literal .wizard), .controlledBy .you])
  fraUntargeted
    (.bind ⟨0⟩ (Instruction.createTokensFixed .cadet 1)
      (Instruction.putPlusOne (.diff wizardTokens (.stepObjects ⟨0⟩)) 1))
    "Create a 2/2 colorless Wizard Soldier creature token named Cadet, then put a +1/+1 counter on each other Wizard token you control"

def essenceBurn : Effect :=
  fraSpellOn (.object .battlefield (.all #[
      .any #[.hasColor (.literal .black), .hasColor (.literal .green)],
      .any #[.hasType .creature, .hasType .planeswalker]]))
    (.seq #[
      Instruction.exileIfDiesThisTurn (.target 0),
      Instruction.dealDamageFixed (.targetSlot 0) 5
    ])
    "This spell deals 5 damage to target black or green creature or planeswalker. If that permanent would die this turn, exile it instead"

def fulminousForteSweep : Effect :=
  let oppCreaturesAndWalkers : ObjectExpr :=
    .inZones .battlefield (.all #[
      .any #[.hasType .creature, .hasType .planeswalker],
      .controlledBy .opponent
    ])
  fraUntargeted
    (Instruction.dealDamageFixed (.objects oppCreaturesAndWalkers) 1)
    "This spell deals 1 damage to each creature and planeswalker your opponents control"

def damageToCreatureOrPlaneswalker (n : Nat) : Effect :=
  fraSpell .creatureOrPlaneswalker
    (Instruction.dealDamageFixed (.targetSlot 0) n)
    s!"This spell deals {n} damage to target creature or planeswalker"

def moltenTide : Effect :=
  fraUntargeted
    (.installEffect (.createDelayedTrigger {
      pattern := .activateAbility .you (.all #[.hasSubtype (.literal .mountain), .controlledBy .you]) .manaAbility
      duration := .untilEndOfTurn
      oneShot := false
      effect := { body := Instruction.addSimpleMana #[.colored .red] }
    }))
    "Until end of turn, whenever you tap a Mountain for mana, add an additional {R}"

/-! ## Green -/

def enroot : Effect :=
  fraUntargeted
    (.player (.searchLibrary {
      zones := .libraryOf .you
      filter := .hasType .land
      count := .upTo (.const 1)
      dest := .graveyard
      reveal := false
      shuffle := true
    }))
    "Search your library for a land card, put it into your graveyard, then shuffle"

def flourishingGrapple : Effect :=
  fraSpell (.ofSlots #[
      .of (.object .battlefield (.all #[
        .any #[.hasType .creature, .hasType .planeswalker],
        .controlledBy .opponent,
        .any #[.hasColor (.literal .red), .hasColor (.literal .white)]])),
      .of .creatureYouControl])
    (.seq #[
      Instruction.loseAllAbilities (.target 0),
      Instruction.dealDamage (.targetSlot 0) (.objectStat .power (.target 1)) (.target 1)
    ])
    "Target creature or planeswalker an opponent controls that's red or white loses all abilities until end of turn. Target creature you control deals damage equal to its power to that permanent"

def restoreWithEmpathy : Effect :=
  fraSpell .permanentCardInYourGraveyard
    (.seq #[
      .moveZone (.target 0) (.hand .controller) .returnToHand {},
      Instruction.gainLifeFixed 4
    ])
    "Return target permanent card from your graveyard to your hand. You gain 4 life"

def somethingWorthSaving : Effect :=
  fraUntargeted
    (.seq #[
      .player (.inspectLibrary {
        source := .millCards .you (.const 4)
        action := .takeMatching (.isKind .permanentCard) (.upTo (.const 1)) (.hand .controller)
        rest := .leaveInPlace
      }),
      Instruction.gainLifeFixed 1
    ])
    "Mill four cards. You may put a permanent card from among them into your hand. You gain 1 life"

def tethermagesAdvantage : Effect :=
  fraSpell .creature
    (.seq #[
      Instruction.pumpFixed (.target 0) 2 2,
      Instruction.grantKeywords (.target 0) #[Keyword.reach],
      Instruction.untap (.target 0)
    ])
    "Target creature gets +2/+2 and gains reach until end of turn. Untap it"

/-! ## Multicolor -/

def creaturesYouControlGetUntilEot (p t : Int) : Effect :=
  fraUntargeted
    (Instruction.pumpFixed creaturesYouControlExpr p t)
    s!"Creatures you control get {signedStat p}/{signedStat t} until end of turn"

def chargeTheSanctumPump : Effect :=
  fraSpell .creature
    (.seq #[
      Instruction.pumpFixed (.target 0) 2 0,
      Instruction.grantKeywords (.target 0) #[Keyword.firstStrike],
      Instruction.putPlusOne (.target 0) 1
    ])
    "Target creature gets +2/+0 and gains first strike until end of turn. Put a +1/+1 counter on it"

def clashOfElements : Effect :=
  fraSpell .nonland
    (.optional (.ownerOf (.target 0)) none
      (.seq #[
        Instruction.putOnLibrary (.target 0) .top,
        Instruction.dealDamageFixed (.players (.ownerOf (.target 0))) 2
      ])
      (Instruction.putOnLibrary (.target 0) .bottom))
    "Choose target nonland permanent. Its owner may put it on top of their library. If they do, this spell deals 2 damage to them. If they didn't put the card on top of their library, they put it on the bottom"

def entrustTheSpark : Effect :=
  fraUntargeted
    (Instruction.may .you
      (some (CostSpec.ofItem (.sacrifice (.count (.const 1)) (.filter (.hasType .planeswalker)))))
      (.player (.searchLibrary {
        zones := .libraryOf .you
        filter := .hasType .planeswalker
        count := .upTo (.const 1)
        dest := .battlefield .controller
        reveal := false
        shuffle := true
      })))
    "You may sacrifice a planeswalker. If you do, search your library for a planeswalker card, put it onto the battlefield, then shuffle"

def drawThenEmpower (cards n : Nat) : Effect :=
  fraUntargeted
    (.seq #[Instruction.drawFixed cards, Instruction.empowerJace n])
    s!"Draw {cardPhrase cards}. Empower Jace {n}"

def bounceSpellOrCreature : Effect :=
  fraSpell .spellOrCreature (Instruction.bounce (.target 0))
    "Return target spell or creature to its owner's hand"

def damageToCreatureWithFlying (n : Nat) : Effect :=
  fraSpell .creatureWithFlying
    (Instruction.dealDamageFixed (.targetSlot 0) n)
    s!"This spell deals {n} damage to target creature with flying"

def plusOneThenGrant (n : Nat) (k : Array KeywordAbility) (upToOne := false) : Effect :=
  let spec : TargetSpec :=
    if upToOne then .single { domain := .creature, count := .upTo 1 } else .creature
  fraSpell spec
    (.seq #[Instruction.putPlusOne (.target 0) n, Instruction.grantKeywords (.target 0) k])
    s!"Put {plusOnePlusOneCountersPhrase n} on {spec.noun}. It gains {KeywordAbility.joinedAnd k} until end of turn"
    (allowsZeroTargets := upToOne)

def addColorless (n : Nat) : Effect :=
  fraUntargeted
    (Instruction.addSimpleMana (Array.replicate n .colorless))
    s!"Add {String.join (List.replicate n "{C}")}"

def recursiveRecruitment : Effect :=
  fraUntargeted
    (.bind ⟨0⟩ (Instruction.createTokensFixed .cadet 2)
      (Instruction.ifThen (.castPred (.castFrom .graveyard .this))
        (Instruction.putCounters (.stepObjects ⟨0⟩) .plusOnePlusOne
          (.binary .divFloor (.playerMetric .graveyardSize .you) (.const 3)))))
    "Create two 2/2 colorless Wizard Soldier creature tokens named Cadet. If this spell was cast from a graveyard, put a +1/+1 counter on each of them for every three cards in your graveyard"

def targetCreatureGains (k : Array KeywordAbility) (words : String := KeywordAbility.joinedAnd k) : Effect :=
  fraSpell .creature (Instruction.grantKeywords (.target 0) k)
    s!"Target creature gains {words} until end of turn"

def cadetWithHaste : Effect :=
  fraUntargeted
    (.create (.tokens .you (.const 1) .cadet { grantKeywordsUntilEot := #[Keyword.haste] }))
    "Create a 2/2 colorless Wizard Soldier creature token named Cadet. It gains haste until end of turn"

def stingingVitriol : Effect :=
  fraSpell .opponent
    (.seq #[
      Instruction.dealDamageFixed (.targetSlot 0) 2,
      .moveZone (.inZones (.handOf (.target 0)) (.not (.hasType .land))) .graveyard .discard {
        choice? := some { chooser := .controller, count := .exact (.const 1), revealFirst := true }
      }
    ])
    "This spell deals 2 damage to target opponent. That player reveals their hand. You choose a nonland card from it. They discard that card"

def theorixCounter : Effect :=
  fraSpellOn (.object .stack (.all #[.not (.hasType .creature), .isKind .spell]))
    (.unlessPays (.controllerOf (.target 0)) (CostSpec.ofGeneric 2) (Instruction.counter (.target 0)))
    "Counter target noncreature spell unless its controller pays {2}"

def millThenDraw (m d : Nat) : Effect :=
  fraUntargeted
    (.seq #[Instruction.millFixed m, Instruction.drawFixed d])
    s!"Mill {englishNumber m} cards, then draw {cardPhrase d}"

def twinnedVision : Effect :=
  fraUntargeted
    (.ifCond (.not (.castPred (.castFrom .hand .this)))
      (Instruction.drawFixed 2) (Instruction.drawFixed 1))
    "Draw a card. If this spell wasn't cast from your hand, draw two cards instead"

def twistedFates : Effect :=
  let targetPlayerCreatures : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .controlledBy (.ofExpr (.target 1))])
  fraSpell (.ofSlots #[.of .nonland, .of .anyPlayer])
    (.seq #[
      Instruction.destroy (.target 0),
      Instruction.putPlusOne targetPlayerCreatures 1
    ])
    "Destroy target nonland permanent. Put a +1/+1 counter on each creature target player controls"

def permanentYouControlGains (k : Array KeywordAbility) : Effect :=
  fraSpell .permanentYouControl (Instruction.grantKeywords (.target 0) k)
    s!"Target permanent you control gains {KeywordAbility.joinedAnd k} until end of turn"

def vindictiveTriumph : Effect :=
  fraSpell .creatureOrPlaneswalker
    (.moveZone (.target 0) .exile .exile {
      delayedReturn? := some (.returnIfThenExileAtEndStep (.stat .manaValue .le (.const 3)) true .controller)
    })
    "Exile target creature or planeswalker. If that permanent's mana value was 3 or less, return it to the battlefield tapped under your control. Exile it at the beginning of the next end step"

def tamsResistance : Effect := plusOneThenGrant 1 #[Keyword.vigilance] (upToOne := true)

/-! ## Modes of modal triggered abilities -/

def returnLegendaryCardToHand : Effect :=
  fraSpellOn (.object .yourGraveyard (.all #[.hasSupertype .legendary, .isKind .card]))
    (.moveZone (.target 0) (.hand .controller) .returnToHand {})
    "Return target legendary card from your graveyard to your hand"

def plusOneVigilanceIndestructible : Effect :=
  fraSpell .creature
    (.seq #[
      Instruction.putPlusOne (.target 0) 1,
      Instruction.grantKeywords (.target 0) #[Keyword.vigilance, Keyword.indestructible]
    ])
    "Put a +1/+1 counter on target creature. It gains vigilance and indestructible until end of turn"

def fraTapTargetCreature : Effect :=
  fraSpell .creature (Instruction.tap (.target 0)) "Tap target creature"

def untapTargetCreature : Effect :=
  fraSpell .creature (Instruction.untap (.target 0)) "Untap target creature"

def drawThenDiscardOne : Effect :=
  fraUntargeted (.seq #[Instruction.drawFixed 1, Instruction.discardFixed 1])
    "Draw a card, then discard a card"

def destroyNoncreatureNonland : Effect :=
  fraSpellOn (.object .battlefield (.all #[.not (.hasType .creature), .not (.hasType .land)]))
    (Instruction.destroy (.target 0))
    "Destroy target noncreature, nonland permanent"

def gainLifeMode (n : Nat) : Effect :=
  fraUntargeted (Instruction.gainLifeFixed n) s!"You gain {n} life"

def minusPowerPerGraveyard : Effect :=
  fraSpell .creature
    (Instruction.pump (.target 0)
      (.binary .sub (.const 0) (.playerMetric .graveyardSize .you)) (.const 0))
    "Target creature gets -X/-0 until end of turn, where X is the number of cards in your graveyard"

def surveilMode (n : Nat) : Effect :=
  fraUntargeted (Instruction.surveilFixed n) s!"Surveil {n}"

def sourceDealsDamageToCreatureOrPlaneswalker (n : Nat) : Effect :=
  fraSpell .creatureOrPlaneswalker
    (Instruction.dealDamageFixed (.targetSlot 0) n)
    s!"This creature deals {n} damage to target creature or planeswalker"

def createCadetMode : Effect :=
  fraUntargeted (Instruction.createTokensFixed .cadet 1)
    "Create a 2/2 colorless Wizard Soldier creature token named Cadet"

def drawMode : Effect := fraUntargeted (Instruction.drawFixed 1) "Draw a card"

end Effect

namespace ActivatedAbility

/-- An activated ability with its printed line. -/
def fra (printed : String) (effect : Effect) (cost : CostSpec)
    (timing : ActivationTiming := .instant)
    (activeZones : Array ZoneKind := #[.battlefield])
    (condition? : Option Condition := none)
    (lifetimeLimit? : Option Nat := none)
    (tag? : Option ActivationMechanicTag := none)
    (costReductions : Array ActivationCostReduction := #[]) : ActivatedAbility :=
  { cost, effect, printed, timing, activeZones, condition?,
    lifetimeLimit? := lifetimeLimit?.orElse fun _ => if tag? == some .exhaust then some 1 else none,
    tag?, costReductions }

end ActivatedAbility

namespace FraCandidates

/-- Shorthand for an ability effect lowered directly onto `Instruction`. -/
def ab (body : Instruction) (phrase : String) (spec : TargetSpec := .none)
    (allowsZeroTargets := false) (maxTargets := 0) : Effect :=
  { targeting := .of spec, body, phrase, allowsZeroTargets, maxTargets }

end FraCandidates

end Mtg.Engine
