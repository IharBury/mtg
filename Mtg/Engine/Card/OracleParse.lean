import Mtg.Engine.Card.OracleParse.Text
import Mtg.Engine.Card.OracleParse.Phrases
import Mtg.Engine.Card.OracleParse.Costs
import Mtg.Engine.Card.OracleParse.Sentences
import Mtg.Engine.Card.OracleParse.SpellActions
import Mtg.Engine.Card.OracleParse.Lines
import Mtg.Engine.Card.OracleParse.StaticLines
import Mtg.Engine.Card.OracleParse.CatalogSentences
import Mtg.Engine.Card.OracleParse.CatalogEffects
import Mtg.Engine.Card.OracleParse.CatalogLines
import Mtg.Engine.Card.OracleParse.Parse
import Mtg.Engine.Card.OracleParse.Guards
import Mtg.Engine.Card.OracleParse.GuardsLines
import Mtg.Engine.Card.OracleParse.GuardsCatalog

/-!
# Oracle text to card parts

`parseOracleParts` reads printed Oracle text into `CardPart`s.
The parse fails when any part of the text is not recognized, so a card
is not compiled with some of its Oracle text missing.

The parser is split under `OracleParse/`:

- `Text` folds Oracle text and reads mana symbols, keywords, and type lines.
- `Phrases` reads battlefield selectors and until-end-of-turn pumps.
- `Costs` reads activation costs, limits, and stack cost reductions.
- `Sentences` reads one printed sentence, including a modal “choose one” spell.
- `SpellActions` joins the sentences of a spell.
- `Lines` reads Adventure faces and printed triggered, static, and mana lines.
- `StaticLines` reads keyword lines, equipment, and other static abilities.
- `CatalogSentences` reads object descriptions and one catalog sentence.
- `CatalogEffects` reads a catalog effect that spans several sentences.
- `CatalogLines` reads catalog triggers, activated abilities, and statics.
- `Parse` reads one line, a mode list, or an Adventure face, and defines
  `parseOracleParts`.
- `Guards`, `GuardsLines`, and `GuardsCatalog` are the `#guard` regression
  tests, in that order.

Currently recognized:

- comma-separated keyword lines (`Lifelink`, `Flying, deathtouch`),
  including a trailing reminder parenthetical
- Gatherer `//ADV//` Adventure faces: `Name {cost}`, a type line, then
  rules text
- mana symbols `{N}`, `{W}` `{U}` `{B}` `{R}` `{G}`, `{C}`, `{X}`, `{S}`,
  and hybrid `{W/U}`
- `Target <permanent type or …> [you control] gains <keywords> until end of turn.`
- `{cost}: <permanents> [you control] get +N/+N until end of turn.`
- `Pay N life: <permanents or this creature> get +P/+T until end of turn.`
  A following `Activate only once each turn` limits that ability (CR 602.5).
- `{cost}: Put <count> +1/+1 counters on this creature.`
  One counter is `a` or `one` with the singular noun; more than one uses the plural.
- `Sacrifice another <permanent type or …>: Exile the top card of your library. You may play it until the end of your next turn. Activate only during your turn and only once each turn.`
  `another` excludes this object. The activation limit is that timing restriction
  (CR 602.5). The exiled card may be played until the end of your next turn
  (CR 611.2a).
- `{cost}: <this> becomes a <subtype> creature in addition to its other types and gains "<static>".`
  `<this>` is `this`, `this <type>`, the card's name, or the short name before a comma.
  No duration is printed, so the effect lasts until the end of the game (CR 611.2a).
  The quoted text is a static ability this object gains. The static ability recognized
  here is `This creature's power and toughness are each equal to the number of lands you control`
  (CR 208.2a / 604.3). A reminder such as `(This effect doesn't end.)` is not rules text.
- `Tap one or two target <permanents>.`
- `Untap target <permanents> [you control].`
- `It gets +P/+T until end of turn.` (the previous target)
- `If it's a <subtype>, you may attach a/an <subtype> you control to it.`
- `This spell costs {N} less to cast if it targets a tapped creature.`
- `This spell costs {N} less to cast if it targets an attacking nontoken creature.`
- `This spell costs {N} less to cast if a creature died this turn.`
  The reduction is a static ability that functions on the stack (CR 604.2).
- `As an additional cost to cast this spell, sacrifice an <permanent type or …> or pay {N}.`
  The sacrifice and that much generic mana are alternatives (CR 601.2b).
  This functions while the spell is on the stack (CR 113.6 / 604.2).
- `Destroy target <permanent type or …> [with <keyword> | with power N or greater].`
  `N` is a positive printed number. The permanent must have at least that much power.
- `Put a +1/+1 counter on up to one target <permanent type>.`
  Up to one target means zero or one (CR 115.1).
- `Target player gains N life.`
- `You gain N life.`
- `<this card> deals N damage to target <permanent type>.`
  The source is `this`, `this <type>`, the card's name, or the short name
  before a comma (`Bilbo Baggins` for `Bilbo Baggins, Burglar`, CR 201.5).
  `N` is a positive printed number.
- `Whenever this creature attacks, it gets +P/+T until end of turn for each other creature you control.`
- `Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, you gain N life.`
  The ability word has no rules meaning (CR 207.2c). The “while” clause is
  part of the trigger condition (CR 603.2) and is not checked again on
  resolution. The word may be omitted.
- `Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, this creature gets +P/+T until end of turn.`
  The same ability word and “while” clause. The bonus is on this creature.
- `Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +P/+0 and creatures you control gain trample.`
  The same ability word and “while” clause. The bonus and trample both last
  until end of turn. Toughness is unchanged, and the power bonus is not zero.
- `Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, put a +1/+1 counter on each creature you control.`
  The same ability word and “while” clause. One counter goes on each of those creatures.
- `Ferocious — Whenever you attack while you control a creature with power 4 or greater, you draw a card and lose 1 life.`
  The ability word may be omitted. “Whenever you attack” is one trigger when
  creatures you control attack at the same time (CR 508.3 / 603.2d). The
  “while” clause is part of that trigger condition.
- `Ferocious — At the beginning of combat on your turn, if you control a creature with power 4 or greater, put a +1/+1 counter on this creature.`
  The ability word may be omitted. Beginning of combat is CR 507.1. The “if”
  is an intervening if (CR 603.4): it is checked when combat begins and again
  when the ability resolves.
- `Landfall — Whenever a land you control enters, put a +1/+1 counter on target <permanent type> you control.`
  `Landfall` is an ability word (CR 207.2c) and may be omitted.
- `Landfall — Whenever a land you control enters, this creature gets +P/+T until end of turn.`
  `Landfall` may be omitted. The bonus is on this creature and lasts until end of turn.
- `Whenever another Elf you control enters, this creature gets +1/+1 until end of turn.`
  `another` excludes this object.
- `{T}: Add X mana of any one color, where X is <this>'s power. Spend this mana only to cast Elf spells and activate abilities of Elf sources.`
  `<this>` is `this creature` or the card's name. The tap symbol is the cost (CR 107.5).
  That mana can be spent only on Elf spells and activated abilities of Elf sources.
- `<this>'s power and toughness are each equal to the number of lands you control.`
  A characteristic-defining ability (CR 208.2a / 604.3). `<this>` is `this creature`
  or the card's name.
- `You may play an additional land this turn.`
- `When <this card> enters, search your library for a Forest card, put that card onto the battlefield, then shuffle.`
  The entering object is `this`, `this <type>`, the card's name, or the short name
  before a comma.
- `When <this card> enters, draw a card.` / `draw N cards.`
  The entering object is `this`, `this <type>`, the card's name, or that short name
- `When <this card> enters, put a +1/+1 counter on target <permanent type>.`
  The entering object is the same. The counter goes on that target.
- `When <this card> enters, recruit.`
  Recruit is a keyword action of this card's controller. A trailing reminder
  parenthetical is not rules text (CR 207.2).
- `When <this card> dies, target <permanent type or …> an opponent controls gets P/T until end of turn.`
  The dying object is `this`, `this <type>`, the card's name, or that short name.
  `P/T` is a signed change such as -1 / -1
- `Whenever one or more other creatures die, scry N.`
  Those creatures die at the same time (CR 603.2c).
- `Whenever you sacrifice a token, target opponent loses N life.`
  The token is a permanent this object's controller sacrifices (CR 701.17).
  The opponent is one target.
- `Whenever one or more <objects> you control deal damage to a player, put <count> +1/+1 counters on <this>.`
  Those objects deal that damage at the same time, so this is one trigger
  (CR 603.2c). Combat damage and noncombat damage both count. `<this>` is
  this card's name or the short name before a comma.
- `Whenever you draw your second card each turn, put a +1/+1 counter on this creature.`
- `Whenever you draw a card, put a +1/+1 counter on this creature.`
- `When <this card> enters, target opponent sacrifices a creature of their choice.`
  The entering object is `this`, `this <type>`, the card's name, or that short name.
  The opponent chooses which creature to sacrifice (CR 701.17a)
- `When <this card> enters, each opponent discards a card.`
- `When <this card> enters, he deals N damage divided as you choose among one, two, or three targets.`
  The source is a pronoun for the entering object (`he`, `she`, `it`, or `they`)
  or another reference to this card. Its controller divides the damage
  (CR 601.2d). `targets` with no type is any target. The counts are a
  positive contiguous range.
- `When <this card> enters, you may discard a card. If you do, draw N cards.`
  The draw happens only when that discard is taken.
- `Equipped creature gets +P/+T.`
- `Equip {cost}`
  A trailing reminder parenthetical is not rules text (CR 207.2)
- `Scry N.`
- `Target <permanent type> gets +P/+T until end of turn.`
- `Target <permanent type> gets +P/+T and gains <keywords> until end of turn.`
- `Target creature gets +P/+T until end of turn. If that creature would die this turn, exile it instead.`
  The pump and the replacement both last until end of turn. Dying is being
  put into a graveyard from the battlefield (CR 614.1).
- `<permanent types> target player controls get +P/+T until end of turn.`
  `P/T` may be negative, as in -1 / -1
- `Target player draws <count> cards and loses N life.`
- `Target <permanent> you control deals damage equal to its power to target <permanent> an opponent controls.`
- `Whenever <this card> attacks, choose up to one other target <permanent type> you control. Its base power and toughness become equal to <this card>'s power and toughness until end of turn.`
  The attacker is `this`, `this <type>`, the card's name, or the short name
  before a comma. Up to one target means zero or one (CR 115.1).
- `Choose one —` followed by `•` modes:
  - `Counter target spell unless its controller pays {cost}.`
  - `Draw <count> cards, then discard <count> card(s).`
  - `Target <permanent type> gets +P/+T until end of turn.`
  - `Target <permanent type> gets +P/+T and gains <keywords> until end of turn.`
  - `Target creature gets +P/+T until end of turn. If that creature would die this turn, exile it instead.`
  - `<permanent types> target player controls get +P/+T until end of turn.`
  - `Target player draws <count> cards and loses N life.`
  - `Destroy target <permanent type or …> [with <keyword> | with power N or greater].`
  - `Destroy target <permanent type or …>. You gain N life.`
  - `<permanents> you control get +P/+T until end of turn.`
  - `Until end of turn, target creature becomes an artifact in addition to its other types and gains indestructible.`
    A trailing reminder parenthetical is not rules text (CR 207.2).
  - `Put a +1/+1 counter on target <permanent> [you control]. It gains <keywords> until end of turn.`
- `Counter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled.`
- `<this card> can't be blocked.`
  The subject is `this`, `this <type>`, the card's name, or the short name
  before a comma
- `<this card> can't be blocked by tokens.`
  The subject is the same. Tokens cannot be declared as blockers for it.
- `<this card> can't block.`
  The subject is the same as for “can't be blocked”
- `When <this card> enters, exile up to one target card from an opponent's graveyard. Each opponent loses N life.`
- `{cost}, Sacrifice an <permanent type or …>: Return this card from your graveyard to your hand. Activate only as a sorcery.`
  Returning this card from a graveyard functions while the card is in that
  graveyard (CR 113.6), so the ability is `graveyardActivatedIf`
- `Whenever <this card> deals combat damage to a player, draw <count> cards, then discard <count> card(s).`
- `Exchange control of <count> target nonland permanents that share a card type.`
- `Target <permanent type>'s owner puts it on their choice of the top or bottom of their library.`
- `<this> enters tapped.`
  A replacement effect (CR 614.1). `<this>` is `this`, `this <permanent type>`,
  the card's name, or the short name before a comma.
- `{T}: Add {A} or {B}.`
  Two or more colored or colorless symbols, joined by `or`. The tap symbol is
  the cost (CR 107.5). The player adds one of them.
- `{cost}: Target creature can't be blocked this turn.`
  The restriction lasts until end of turn.
- `Put <count> +1/+1 counters on target <creature type> [you control].`
  One counter is `a` or `one` with the singular noun; more than one uses the
  plural. A creature type is `Elf`, `Goblin or Orc`, or `Bear, Spider, or Wolf`:
  a creature of those subtypes. Costs separated by commas may include mana,
  `{T}`, and `Sacrifice <this>`. `Activate only as a sorcery` is the timing
  restriction (CR 602.5a).
- `{T}, Sacrifice <this>: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle.`
- `{T}, Pay N life, Sacrifice <this>: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle. You may behold a <subtype>. If you do, untap that land.`
  Behold is a keyword action (CR 701.4). The land on the battlefield is
  `affectedByAction` of the numbered `putOntoBattlefieldInState`; the
  search variable still names the library card (CR 400.7). That land untaps
  only when that behold happened (CR 701.4b). A trailing reminder
  parenthetical is not rules text.
- `<type>cycling {cost}`
  Typecycling (CR 702.29). `<type>` is a subtype (`Halflingcycling`), a card
  type, or supertypes plus a type (`Basic landcycling`). A trailing reminder
  parenthetical is not rules text.
- `When <this> enters, you gain N life.`
- `When <this> enters, untap another target creature you control. If that creature is a <subtype>, put a +1/+1 counter on it.`
- `When <this card> dies, recruit.`
  Recruit is a keyword action of this card's controller. A trailing reminder
  parenthetical is not rules text (CR 207.2).
- `When <this card> enters, scry N.`
  `N` is a positive printed number.
- `When <this card> enters, create a Treasure token.`
  `create a tapped Treasure token` creates that token tapped (CR 110.5).
- `When <this card> enters, exile the top card of your library. Until the end of your next turn, you may play that card.`
  The exiled card may be played until the end of your next turn (CR 611.2a).
- `{cost}: Add one mana of any color.`
  Costs separated by commas may include mana, `{T}`, and `Sacrifice <this>`.
- `{cost}: Destroy target permanent.`
  The same costs. The permanent is one target.
- `<this>'s power is equal to the number of creatures you control.`
  A characteristic-defining ability (CR 208.2a / 604.3). `<this>` is `this creature`
  or the card's name. Toughness is not changed.
- `This spell can't be countered.`
  Countering this spell is forbidden. The ability functions while this spell
  is on the stack (CR 113.6b).
- `Whenever you cast a noncreature spell, amass <subtype>s N.`
  Amass is a keyword action of this card's controller (CR 701.45). The
  subtype is printed in the plural (`Goblins`). `N` is a positive count.
  A trailing reminder parenthetical is not rules text (CR 207.2).
- `Whenever you cast a noncreature spell, you may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard two cards.`
  The spell is that cast. X is the mana spent to cast it (CR 601.2h), not
  its mana value. Discarding two cards happens only when the draw is taken.
- `Recruit.`
  Recruit is a keyword action of this card's controller. A trailing reminder
  parenthetical is not rules text (CR 207.2).
- `Return target <card type> card with mana value N or less from your graveyard to the battlefield.`
  The card is in your graveyard. `N` is a positive printed number. Its mana
  value is at most `N` (CR 202.3).
- `When <this card> enters, amass <subtype>s N.`
  The entering object is `this`, `this <type>`, the card's name, or the short
  name before a comma. Amass is the same keyword action.
- `When <this card> dies, amass <subtype>s N.`
  The dying object is the same. Amass is the same keyword action.
- `Whenever you attack, amass <subtype>s N.`
  “Whenever you attack” is one trigger when creatures you control attack at
  the same time (CR 508.3 / 603.2d).
- `You may cast this spell as though it had flash if you control a <subtype>.`
  The permission is checked as you begin to cast this spell, before the card
  is put onto the stack (CR 601.3 / 702.8). `you` is the player who would cast
  it (`Selector.caster`), not necessarily its controller or owner. The spell
  does not gain flash.
- `<permanents> get +P/+T.`
  No duration is printed, so this is a static ability (CR 604.2 / 613.4c).
  A zero bonus is omitted. `+0/+0` is not an effect. `until end of turn` is a
  different ability.
- `Whenever <this card> enters or attacks, recruit.`
  Recruit is a keyword action of this card's controller. A trailing reminder
  parenthetical is not rules text (CR 207.2).
- `You draw a card and lose 1 life.`
  One card and 1 life. The player is this spell's controller.
- `Amass <subtype>s N.`
  Amass is a keyword action of this spell's controller (CR 701.45). The
  subtype is printed in the plural (`Goblins`). `N` is a positive count.
  A trailing reminder parenthetical is not rules text (CR 207.2).
- `Return up to one target <card type> card from your graveyard to your hand.`
  Up to one target means zero or one (CR 115.1). The card is in your graveyard.
- `Counter target spell. If that spell's mana value was N or less, recruit.`
  The spell is one target. Its mana value is recorded before it is
  countered, while it is still on the stack, so the chosen value of `{X}`
  counts (CR 202.3 / 202.3e / 107.3a). Recruit happens only when that
  recorded value is less than or equal to `N`. Recruit is a keyword action
  of this spell's controller.
  A trailing reminder parenthetical is not rules text (CR 207.2).
  Successive spell lines are one effect, in printed order.
- `Whenever an artifact you control enters, draw a card.`
  One card. The entering permanent is an artifact this object's controller
  controls.
- `<this> can't attack unless you control <count> or more other <subtypes>.`
  `<this>` is `this`, `this <type>`, the card's name, or the short name
  before a comma. `<count>` is a positive count (`two`). The subtype is
  printed in the plural (`Wolves`). Attacking is forbidden while that player
  controls fewer than `<count>` other permanents of that subtype.
- `At the beginning of your upkeep, create a <P>/<T> <color> <subtype> creature token.`
  `your` is this object's controller (CR 503.1). The token is one creature
  of that power, toughness, color, and subtype. `create <count>` uses the
  plural `tokens` when the count is greater than one.
- `When <this> enters, create a <P>/<T> <color> <subtype> creature token, then attach <this> to it.`
  The entering object is this card. One token is created, and this object
  is attached to that token.
- `When <this> enters, amass <subtype>s N, then attach <this> to the amassed Army.`
  The entering object is this card. Amass is a keyword action of this card's
  controller. This object is attached to the Army that action amassed.
  A trailing reminder parenthetical is not rules text (CR 207.2).
- `Equipped creature gets +P/+T and has <keywords>.`
  Also `Enchanted creature gets +P/+T and has <keywords>.`
  The bonus and the keywords are static abilities of the Equipment or Aura
  (CR 604.1 / 301.5 / 303.4). `and has ward {N}` is that much generic ward
  instead of keywords. `and has` may be omitted when there is neither.
  A zero bonus on one side is omitted. `+0/+0` is not an effect.
- `Put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control.`
  The creature is one target. `each other` is every other creature that
  spell's controller controls. The extra counters are put only when this
  spell was cast from a graveyard. That cast is an event since the start of
  the game (CR 601.2 / 702.34).
- `Flashback {cost}`
  The card may be cast from a graveyard for that cost (CR 702.34). A trailing
  reminder parenthetical is not rules text.
- `Draw <count> cards. If this spell was cast from a graveyard, draw <count> cards instead.`
  The second draw replaces the first when this spell was cast from a
  graveyard. That cast is an event since the start of the game
  (CR 601.2 / 702.34). One card is `a card`; more than one is plural.
- `Amass <subtype>s N. If this spell was cast from a graveyard, amass <subtype>s M instead.`
  The second amass replaces the first in that same case. Both amass the
  same subtype. A trailing reminder parenthetical is not rules text.
- `Put <count> +1/+1 counters on target creature you control. Then it fights target creature an opponent controls.`
  The creature you control is one target. The opponent's creature is
  another. One counter uses the singular noun. A trailing reminder
  parenthetical is not rules text.
- `Enchant <permanent>.`
  Enchant (CR 702.5). The permanent is one target. `Enchant creature` is
  a creature.
- `Ward {N}`
  Ward (CR 702.21). `N` is a positive generic cost. A trailing reminder
  parenthetical is not rules text.
- `{cost}: <this>'s owner shuffles <object> into their library and draws <count> cards.`
  `<this>` is this card's name or `this <type>`. `<object>` is `him`,
  `her`, `them`, `it`, or another reference to this card. The owner is
  recorded before the shuffle, and that player draws afterward.
- `{cost}: Return this card from your graveyard to the battlefield attached to target creature you control with power N or less. Activate only as a sorcery.`
  Returning this card from a graveyard functions while the card is in that
  graveyard (CR 113.6), so the ability is `graveyardActivatedIf`. The card
  enters the battlefield already attached to that creature (CR 303.4f).
  `N` is a positive printed power. The creature is one target.
- `When <this> enters, attach <object> to target <permanent> [you control].`
  The entering object is this card. `<object>` is `it` or this card. A
  creature type such as `Dwarf` is a creature of that subtype.
- `Each creature you control with a +1/+1 counter on it has menace.`
  A trailing reminder parenthetical is not rules text.
- `At the beginning of your end step, draw a card.`
  `your` is this object's controller (CR 513.1). One card.
- `Search your library for a legendary creature card, reveal it, put it into your hand, then shuffle.`
  The searcher chooses one legendary creature card (CR 701.19). A trailing
  reminder parenthetical is not rules text.
- `<this> has haste as long as you control another <subtype>.`
  `<this>` is `this`, `this <type>`, the card's name, or the short name
  before a comma. The subtype is singular (`Goblin`). This has haste while
  its controller controls another permanent of that subtype.
- `{cost}, Sacrifice another <subtype>: Add {mana}.`
  Sacrificing another permanent of that subtype you control is part of the
  cost. The controller adds that mana.
- `{cost}: Draw a card, then discard a card.`
  One card drawn, then one card discarded.
- `Whenever <this> attacks, target attacking creature gains <keywords> until end of turn.`
  The attacker is `this`, `this <type>`, the card's name, or the short name
  before a comma.
- `This spell costs {X} less to cast, where X is the total power of creatures you control with flying.`
  The printed reduction is `{X}`, and X is that total power (CR 601.2f / 107.3).
  The ability functions on the stack (CR 604.2).
- `When <this> enters, search your library for a basic land card, reveal it, put it into your hand, then shuffle.`
  The searcher chooses one basic land card (CR 701.19).
- `When <this> enters, it deals N damage to any target. If a <subtype> is dealt damage this way, destroy it.`
  The source is `it`, `he`, `she`, `they`, or another reference to this card.
  `N` is a positive printed number. `any target` is a player or creature.
  The damage is a numbered action. The object of that action is destroyed
  only when the damage is dealt to it and it has the subtype. Prevented
  damage does not destroy it.
- `Whenever <this> attacks, he deals damage equal to the number of Treasures you control to any target.`
  The source is a pronoun or another reference to this card. The amount is
  how many Treasure artifacts its controller controls.
- `At the beginning of your upkeep, create a Treasure token.`
  `your` is this object's controller (CR 503.1).
- `Whenever an opponent casts their first noncreature spell each turn, you recruit.`
  Recruit is a keyword action of this card's controller. A trailing reminder
  parenthetical is not rules text (CR 207.2).
- `As long as you have an enduring story, <this> gets +P/+T and has <keywords>.`
  `<this>` is this card. A zero bonus is omitted. `+0/+0` with no keywords
  is not an effect.
- `As long as you have an enduring story, creatures you control get +P/+T.`
  A zero bonus is omitted. `+0/+0` is not an effect.
- `As long as you have an enduring story, artifacts and creatures you control have ward {N}.`
  `N` is a positive generic cost.
- `As long as you have an enduring story, creatures can't attack you unless their controller pays {N} for each of those creatures.`
  `you` is this object's controller. `N` is a positive generic cost.
- `<this> doesn't untap during your untap step unless you have an enduring story.`
  `<this>` is this card. `your` is its controller (CR 502.3).
- `Whenever <this> or another nontoken <subtype> you control enters, create a <P>/<T> <color> <subtype> creature token.`
  `<this>` is this card. `another` excludes this object. One token is created.
- `{cost}, Discard a card: Draw a card.`
  Costs separated by commas may include mana, `{T}`, and discarding one card
  from hand. One card is drawn.
- `When <this> enters, you gain N life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top.`
  The entering object is this card. The searcher chooses one basic land
  card (CR 701.19). That card is held out of the shuffle, then put on top.
- `Threshold — <this> gets +P/+T as long as there are seven or more cards in your graveyard.`
  `Threshold` is an ability word (CR 207.2c / 702.62) and may be omitted.
  Seven or more cards in your graveyard is that ability. A zero bonus is
  omitted. `+0/+0` is not an effect.
- `Mill <count> cards, then put an instant or sorcery card from among them into your hand.`
  More than one card uses the plural `cards`. One instant or sorcery card
  from among the milled cards goes to hand.
- `Exile two target creatures and/or lands you control, then return them to the battlefield under their owner's control.`
  Those two permanents are the targets. They return under their owner's
  control, not tapped.
- `Choose one or both —` followed by `•` modes. The controller selects one
  or two distinct modes (CR 700.2).
- `<this card> deals N damage to target creature. If that creature would die this turn, exile it instead.`
  The damage is dealt to one creature. Dying this turn is replaced by exile.
- `Destroy target artifact token.`
- `Mill <count> cards, then put up to <count> land card(s) from among them into your hand.`
  More than one milled card uses the plural `cards`. Up to one land card is
  singular; more than one is plural. Zero lands may be chosen.
- `<this card> deals N damage to each creature your opponents control.`
- `<this card> deals N damage to each non-Dragon creature.`
  `Add <count> mana in any combination of colors. Spend this mana only to cast <subtype> spells.`
  The mana is one addition in any combination of colors. That mana can be
  spent only on spells of that subtype.
- `Other <plural creature type> you control get +P/+T.`
  No duration is printed, so this is a static ability. `Elves` is Elf.
- `Landfall — Whenever a land you control enters, create a <P>/<T> <color> <subtype> creature token.`
  `Landfall` may be omitted.
- `<this> enters tapped unless you control an Equipment.`
  It enters tapped while its controller controls no Equipment. The ability
  functions in every zone (CR 113.6) so it can replace how this card enters
  the battlefield.
- `{cost}: Create a <P>/<T> <color> <subtype> creature token. This ability costs {N} less to activate for each Equipment you control. Activate only as a sorcery.`
  `{N}` is generic mana. The reduction is a static effect of that activated
  ability, not a separate ability and not a reduction of this card.
- `At the beginning of your first main phase, add {mana}.`
  `your` is this object's controller (CR 505.1).
- `When <this> enters, attach target Equipment you control to up to one target creature you control.`
  Up to one target means zero or one (CR 115.1).
- `<this> can't be blocked by creatures with power N or less.`
  `N` is a positive printed power.
- `Whenever <this> becomes the target of a spell or ability an opponent controls, draw a card.`
  One ability, even if that spell or ability targets this more than once.
- `Whenever you attack, recruit.`
  “Whenever you attack” is one trigger when creatures you control attack at
  the same time (CR 508.3 / 603.2d). A trailing reminder parenthetical is
  not rules text.
- `Crew N`
  Crew (CR 702.122). `N` is the number of creatures to tap. A trailing
  reminder parenthetical is not rules text.
- `Teamwork N`
  Teamwork (CR 702.194). `N` is a positive total power. A trailing reminder
  parenthetical is not rules text.
- `Improvise`, `Boast`, `Cascade`, `Extort`
  Each is that keyword. `Cascade, cascade` is two instances. A trailing
  reminder parenthetical is not rules text.
- `Kicker {cost}`
  Kicker (CR 702.32). `{cost}` is mana symbols. A trailing reminder
  parenthetical is not rules text.
- `Affinity for <type>`
  Affinity (CR 702.40). `<type>` is a plural card type (`artifacts`) or the
  English plural of one subtype (`Elves`). A trailing reminder parenthetical
  is not rules text.
- `Sneak {cost}`
  Sneak. `{cost}` is mana symbols. A trailing reminder parenthetical is not
  rules text.
- `Equip abilities you activate that target this creature cost {N} less to activate.`
  `{N}` is generic mana. Those equip abilities cost that much less.
- `Equipped creature has <keywords> and can't be blocked.`
  The equipped creature has those keywords and can't be blocked.
- `Equip—{cost}, Pay N life.`
  The Equip keyword (CR 702.6). The cost is that mana plus `N` life.
  `N` is a positive life payment. Equip only as a sorcery.
- `As an additional cost to cast this spell, sacrifice a creature.`
  The sacrifice is announced as the spell is cast (CR 601.2b). On an
  Adventure face, a following `Draw a card` / `Draw N cards` is that face's
  effect. A draw with no other text is still unrecognized on a main face.
- `{cost}, {T}, Sacrifice this creature: Search your library for up to two basic land cards, reveal them, put one onto the battlefield tapped and the other into your hand, then shuffle.`
  Up to two is zero, one, or two. One of the found cards enters tapped.
  The rest go to hand.
- `Landfall — Whenever a land you control enters, choose one —`
  then `• Tap target creature an opponent controls.` and
  `• Untap target creature you control.`
  `Landfall` may be omitted. Exactly one mode is chosen.
- `Landfall — Whenever a land you control enters, you may have this creature's base power and toughness become P/T until end of turn.`
  `Landfall` may be omitted. The change is optional and ends at the cleanup step.
- `When this creature enters, return up to one other target permanent you control to its owner's hand. If you do, put a +1/+1 counter on this creature.`
  Up to one target is zero or one (CR 115.1). The counter is put only when a
  permanent is returned.
- `As long as you have an enduring story, you may pay {0} rather than pay the equip cost of the first equip ability you activate each turn.`
  An alternative cost of `{0}` for Equip abilities of permanents that player controls (CR 118.9), not a cost reduction. It is available only when that player has not activated one since the turn began.
- `Whenever another Dwarf or Equipment you control enters, draw a card. This ability triggers only once each turn.`
  Another permanent that is a Dwarf or an Equipment. The trigger happens at
  most once each turn.
- `<this> has lifelink as long as you control another <subtype>.`
  This has lifelink while its controller controls another permanent of that
  subtype. The subtype is singular.
- `When <this> enters, look at the top <count> cards of your library. You may reveal a <subtype> or <subtype> card from among them and put it into your hand. Put the rest on the bottom of your library in a random order.`
  One card uses the singular. The revealed card is one of those two subtypes.
- `When <this> enters, create X tapped Treasure tokens, where X is the number of artifacts your opponents control.`
  X is how many artifact permanents those opponents control.
- `Whenever you cast a spell, if mana from a Treasure was spent to cast it, you draw a card and lose 1 life.`
  The ability triggers once when that spell is cast, not once for each mana
  spent. First, mana from a Treasure — any object with that subtype — is
  spent to cast a spell this object's controller casts. That cast is
  numbered. Then that spell, argument 1 of the numbered cast, is cast. The
  payment happens before the spell becomes cast (CR 601.2h / 601.2i). The
  “if” is an intervening if (CR 603.4). One card and 1 life.
- `Instant and sorcery spells you cast cost {X} less to cast, where X is equipped creature's power.`
  The printed reduction is `{X}`. X is the equipped creature's power.
- `Mill six cards, then put all instant and sorcery cards from among them into your hand.`
  More than one card uses the plural `cards`. Every instant and sorcery card
  from among them goes to hand.
- `Mill four cards, then put all Elf cards from among them into your hand.`
  More than one card uses the plural `cards`. The subtype is singular
  (`Elf`, not `Elves`). Every card of that subtype from among them goes to hand.
- `Exile all attacking creatures target player controls. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle.`
  The player is one target. “That many” is how many of those creatures are
  exiled. That player chooses whether to search, and may find any number
  from zero up to that many (CR 701.19b). The lands enter tapped.
- `When <this> enters, create a colorless Equipment artifact token named <name> with "<equipped creature gets +P/+T>" and equip {cost}.`
  The token is a colorless Equipment artifact with that name. Colorless is
  an empty color indicator. A zero bonus is omitted. `+0/+0` is not an effect.
- `Whenever you cast a noncreature spell, <this> gets +P/+T until end of turn and deals N damage to each opponent.`
  `<this>` is this card. The bonus lasts until end of turn. `N` is a positive
  count. Each opponent of this object's controller is dealt that damage.
- `Look at the top <count> cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a <subtype>.`
  One card uses the singular. Those cards are exiled face down. You may play
  them while they remain exiled and you control a permanent of that subtype.
- `When <this> enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card.`
  The power and controller are the creature's last-known information
  (CR 608.2h). With no target, no player amasses and no card is drawn.
- `Whenever <this> or another <subtype> you control enters, you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, <this> deals X damage to each opponent.`
  X is how many cards were discarded. Declining discards nothing, so no
  cards are drawn and no damage is dealt. An empty hand may be discarded.
- `As this enchantment enters, choose a creature type.` followed by `Creatures you control of the chosen type get +P/+T.`
  Its controller chooses as it enters (CR 614.12). The bonus applies to
  creatures of that type. A zero bonus is omitted.
- `Create X <P>/<T> <color> <subtypes> creature tokens.`
  X is the value of X (CR 107.3). The noun is plural.
- `{X}{X}, {T}, Sacrifice this land: Create X Treasure tokens.`
  X is the value of X in the activation cost (CR 107.3). The noun is plural.
- `Power-up — <costs>: <effect>`, with the power-up reminder text.
  The ability may be activated only once, and costs this card's mana cost
  less if this card entered this turn. The mana cost is passed as `manaCost`;
  without it the line is not recognized.
- `<effect>. He gains <keywords> until end of turn.` and `Destroy up to one
  target artifact or enchantment. Put a +1/+1 counter on She-Hulk.`
  `He` and `she` are this card.
- `Create a 2/2 colorless Robot Villain artifact creature token.`
  Colorless is an empty color indicator.
- `Each opponent discards a card.`
- `Whenever you draw a card, if you control another Hero, <this> deals N damage to target opponent.`
  The condition is checked on resolution.
- `Whenever <this> attacks, draw a card if her power is 4 or greater.`
  Her power is checked on resolution.
- `<object> with power N or less` and `<object> with power N or greater`.
  For `or greater`, `N` is positive.
- `{T}: Add {C} for each Food you control.` and `Add {R} for each artifact your opponents control.`
  One addition of that mana for each matching permanent.
- `{T}: Add two mana in any combination of {U}, {B}, and/or {R}.`
- `{T}: Add {R}{R}. Spend this mana only to cast Dwarf, Equipment, and Saga spells.`
  The mana can't be spent on anything else this turn (CR 106.6).
- `{T}, Pay 1 life: Add {B} or {R}.`
- `Sacrifice <this> and a legendary artifact` as one item of a cost list.
- `Activate only if you control a legendary creature.`
- `{cost}: Return this card from your graveyard to the battlefield tapped. Activate only if you control <object>.`
  The ability functions in a graveyard (CR 113.6).
- `Choose up to two creatures, then destroy the rest.`
- `Then if you don't control <object>, <effect>.`
- `<this> enters tapped unless you control <object>.`
- `<this> can't block unless you control <object>.`
- `<this>'s power is equal to the number of cards in your hand.`
  A characteristic-defining ability (CR 604.3).
- `<objects> get +P/+T and have ward {N}.`
- `Other <subtypes> you control have "<activated ability>."`
- `<this> deals damage equal to the number of <objects> to each opponent.`
- `Target creature with power N or less can't be blocked this turn.`
- `You may pay {cost}. If you do, <effect>.`
- `You may tap any number of untapped <objects>. Draw a card for each <subtype> tapped this way.`
- `Return target <subtype> card from your graveyard to your hand. You gain life equal to that card's power.`
- `Destroy all <objects>. You gain 1 life for each permanent destroyed this way.`
- `Choose a creature type. Return all creatures that aren't of the chosen type to their owners' hands.`
- `Draw cards equal to the greatest toughness among creatures you control, then put any number of creature cards from your hand onto the battlefield.`
- `<this> gets +X/+0 until end of turn, where X is the greatest power among creatures you control.`
- `Add one mana of any color. Spend this mana only to cast a <subtype> spell or to activate an ability of a <subtype> source.`
  Also `Spend this mana only to cast an <type> spell.` and `Add <mana>. This mana can't be spent to cast a non<type> spell.` (CR 106.6).
- `{T}: Add {A} or {B}. Activate only if this land entered this turn or if you control a basic land.`
- `Look at the top <count> cards of your library. You may reveal a <subtype> card from among them and put it into your hand. Put the rest on the bottom of your library in any order.`
  The owner orders the rest (CR 401.4).
- `<this> deals N damage to each creature.`
- `Destroy target land. Its controller may search their library for a basic land card, put it onto the battlefield tapped, then shuffle.`
- `Double target creature's power and toughness until end of turn.`
  It gets +X/+Y where X and Y are its power and toughness (CR 701.10b).
- `Target creature you control fights target creature an opponent controls.`
- `Target creature you control deals damage equal to twice its power to target creature an opponent controls.`
- `This spell costs {N} less to cast if there are <count> or more <type> cards in your graveyard.`
- `Exile all creatures. Each player may put any number of creature cards from their hand onto the battlefield. Then put all cards exiled this way into their owners' hands. Exile <this>.`
- `{cost}: Harness <this>.` Harness is a keyword action (CR 701.64): if this
  permanent isn’t harnessed, it becomes harnessed. A reminder parenthetical
  is not rules text.
- `∞ — At the beginning of <phase>, <effect>.` ∞ is a keyword ability
  (CR 702.186): as long as this permanent is harnessed, it has that ability.
-/
