import Mtg.Engine.Card.Definition
import Mtg.Engine.Card.LineCache

/-!
# Oracle text to card parts

`parseOracleParts` reads printed Oracle text into `CardPart`s.
The parse fails when any part of the text is not recognized, so a card
is not compiled with some of its Oracle text missing.

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

namespace Mtg.Engine

namespace OracleParts

open Cache

/-!
The catalog compiles by evaluating `parseOracleParts` on every card. Each
candidate parser case-folds and splits the same line, so these helpers remember
the last result for a string object (`OracleParts.Cache`). A copy with the same
characters misses and is folded again, which is the same result.

A cache miss runs only the pure body. Those bodies do not call the cached
wrappers, so one lookup does not re-enter another.
-/

def lowerAscii : String → String := CardDef.lowerAscii

def stripReminderParenthetical : String → String := CardDef.stripReminderParenthetical

def stripTrailingPeriod (s : String) : String :=
  let s := s.trimAscii.copy
  if s.endsWith "." then (s.dropEnd 1).trimAscii.copy else s

/-- Trimmed copy of `s`. -/
private def copiedPure (s : String) : String :=
  s.trimAscii.copy

private unsafe def copiedFast (s : String) : String :=
  cachedAt copiedCache s copiedPure

@[noinline, implemented_by copiedFast]
def copied (s : String) : String :=
  copiedPure s

/-- Case-folded Oracle text. -/
private def normPure (s : String) : String :=
  lowerAscii (copiedPure s)

private unsafe def normFast (s : String) : String :=
  cachedAt normCache s normPure

@[noinline, implemented_by normFast]
def norm (s : String) : String :=
  normPure s

/-- Sentences of `text`. A reminder parenthetical is not part of a sentence,
and a trailing period is dropped. -/
private def sentencesPure (text : String) : List String :=
  (stripReminderParenthetical text).splitOn ". "
    |>.map stripTrailingPeriod
    |>.filter (· != "")

private unsafe def sentencesFast (text : String) : List String :=
  cachedAt sentencesCache text sentencesPure

@[noinline, implemented_by sentencesFast]
def sentences (text : String) : List String :=
  sentencesPure text

/-- Rules text of `line` after a reminder parenthetical is removed.
Empty when the line is only a reminder. -/
private def rulesTextPure (line : String) : String :=
  stripTrailingPeriod (stripReminderParenthetical line)

private unsafe def rulesTextFast (line : String) : String :=
  cachedAt rulesTextCache line rulesTextPure

@[noinline, implemented_by rulesTextFast]
def rulesText (line : String) : String :=
  rulesTextPure line

private def normSentencePure (s : String) : String :=
  normPure (stripTrailingPeriod s)

private unsafe def normSentenceFast (s : String) : String :=
  cachedAt normSentenceCache s normSentencePure

@[noinline, implemented_by normSentenceFast]
def normSentence (s : String) : String :=
  normSentencePure s

private def normLinePure (line : String) : String :=
  normPure (rulesTextPure line)

private unsafe def normLineFast (line : String) : String :=
  cachedAt normLineCache line normLinePure

@[noinline, implemented_by normLineFast]
def normLine (line : String) : String :=
  normLinePure line

#guard norm "Smaug — X" == "smaug — x"
#guard normLine "  Flying. " == "flying"
#guard sentences "Draw a card." == ["Draw a card"]
#guard sentences "Draw a card. You gain 1 life." == ["Draw a card", "You gain 1 life"]

/-- `s` is the printed sentence `expected`, ignoring case and a trailing period. -/
def sentenceIs (s expected : String) : Bool :=
  normSentence s == expected

/-- Text after `lead`, when `s` starts with it.
`drop` returns a slice, so the result is copied before any later `splitOn`. -/
def after? (s lead : String) : Option String :=
  if s.startsWith lead then some (s.drop lead.length).trimAscii.copy else none

/-- Text before `tail`, when `s` ends with it. -/
def before? (s tail : String) : Option String :=
  if s.endsWith tail then some (s.dropEnd tail.length).trimAscii.copy else none

/-- Text strictly between `lead` and `tail`. -/
def between? (s lead tail : String) : Option String :=
  (after? s lead).bind fun mid => before? mid tail

/-- Exactly two pieces of `s` around `sep`. Each piece is trimmed and copied.
Zero or several occurrences of `sep` fail. -/
def split2? (s sep : String) : Option (String × String) :=
  match s.splitOn sep with
  | [a, b] => some (copied a, copied b)
  | _ => none

/-- Printed `<cost>: <effect>` after reminder text and a trailing period
are removed. -/
def splitPrintedAbility? (line : String) : Option (String × String) :=
  split2? (rulesText line) ": "

/-- Pieces of `a`, `a or b`, or `a, b, or c`. -/
def orList (s : String) : List String :=
  let normalized := ((norm s).replace ", or " ", ").replace " or " ", "
  normalized.splitOn ", " |>.map copied |>.filter (· != "")

def natOfDigits? (s : String) : Option Nat :=
  let cs := s.toList
  if cs.isEmpty || !cs.all Char.isDigit then none
  else some (cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)

/-- A printed positive numeral. Words such as `two` are not numerals, and zero
is not a count. -/
def positiveDigits? (s : String) : Option Nat :=
  (natOfDigits? (copied s)).filter (· != 0)

/-- `one` through `ten`, or a numeral. The numeral is read from case-folded
text, so surrounding spaces do not hide it. -/
def englishSmall? (s : String) : Option Nat :=
  let s := norm s
  match s with
  | "one" => some 1
  | "two" => some 2
  | "three" => some 3
  | "four" => some 4
  | "five" => some 5
  | "six" => some 6
  | "seven" => some 7
  | "eight" => some 8
  | "nine" => some 9
  | "ten" => some 10
  | _ => natOfDigits? s

/-- A printed positive count: `two`, `2`. Zero is not a count. -/
def positiveCount (s : String) : Option Nat :=
  (englishSmall? s).filter (· != 0)

/-- Drop a leading `a` / `an`. The remainder is case-folded. -/
def dropArticle? (s : String) : Option String :=
  let s := norm s
  after? s "an " <|> after? s "a "

def colorOfLetter? (s : String) : Option Color :=
  match lowerAscii s with
  | "w" => some .white
  | "u" => some .blue
  | "b" => some .black
  | "r" => some .red
  | "g" => some .green
  | _ => none

def parseOneSymbol (s : String) : Option ManaSymbol :=
  let s := s.trimAscii.copy
  match natOfDigits? s with
  | some n => some (.generic n)
  | none =>
    match lowerAscii s with
    | "x" => some .x
    | "c" => some .colorless
    | "s" => some .snow
    | _ =>
      match colorOfLetter? s with
      | some c => some (.colored c)
      | none =>
        match split2? s "/" with
        | some (a, b) =>
          match colorOfLetter? a, colorOfLetter? b with
          | some ca, some cb => some (.hybrid ca cb)
          | _, _ => none
        | none => none

/-- Mana symbols in `s`, which may be a whole cost such as `{1}{W}`.
Text other than symbols and spaces makes the parse fail. -/
def parseManaSymbols (s : String) : Option (List ManaSymbol) :=
  go s.toList [] [] false
where
  go : List Char → List ManaSymbol → List Char → Bool → Option (List ManaSymbol)
    | [], acc, _, false => some acc.reverse
    | [], _, _, true => none
    | ' ' :: rest, acc, body, false => go rest acc body false
    | '{' :: rest, acc, _, false => go rest acc [] true
    | '}' :: rest, acc, body, true =>
      match parseOneSymbol (String.ofList body.reverse) with
      | none => none
      | some sym => go rest (sym :: acc) [] false
    | c :: rest, acc, body, true => go rest acc (c :: body) true
    | _ :: _, _, _, false => none

/-- Mana symbols, failing when `s` has none. -/
def nonemptyMana? (s : String) : Option (List ManaSymbol) :=
  (parseManaSymbols s).bind fun syms =>
    if syms.isEmpty then none else some syms

/-- `{N}` as a positive generic cost. Zero and any other symbol are not that cost. -/
def positiveGeneric? (s : String) : Option Nat :=
  match nonemptyMana? s with
  | some [.generic n] => if n == 0 then none else some n
  | _ => none

def keywordOfOracle? (s : String) : Option Keyword :=
  match norm s with
  | "flash" => some .flash
  | "haste" => some .haste
  | "vigilance" => some .vigilance
  | "flying" => some .flying
  | "menace" => some .menace
  | "hexproof" => some .hexproof
  | "indestructible" => some .indestructible
  | "reach" => some .reach
  | "trample" => some .trample
  | "deathtouch" => some .deathtouch
  | "defender" => some .defender
  | "lifelink" => some .lifelink
  | "first strike" => some .firstStrike
  | "islandwalk" => some .islandwalk
  | "storied" => some .storied
  | "double strike" => some .doubleStrike
  | "prowess" => some .prowess
  | "ascend" => some .ascend
  | "shadow" => some .shadow
  | "changeling" => some .changeling
  | "improvise" => some .improvise
  | "boast" => some .boast
  | "cascade" => some .cascade
  | "extort" => some .extort
  | _ => none

/-- A line that is only modeled keywords, e.g. `Lifelink` or `Flying, deathtouch`.
One unrecognized word fails the line. -/
def keywordParts? (line : String) : Option (List CardPart) :=
  let cleaned := rulesText line
  if cleaned.isEmpty then none
  else
    let tokens :=
      cleaned.splitOn "," |>.map (·.trimAscii.copy) |>.filter (· != "")
    if tokens.isEmpty then none
    else
      (tokens.mapM keywordOfOracle?).map fun kws =>
        kws.map fun k => .ability (.keyword k)

def supertypeOfOracle? (s : String) : Option CardSupertype :=
  match lowerAscii s with
  | "basic" => some .basic
  | "legendary" => some .legendary
  | "ongoing" => some .ongoing
  | "snow" => some .snow
  | "world" => some .world
  | _ => none

def cardTypes : List CardType := [
  .artifact, .battle, .creature, .enchantment, .instant, .land,
  .planeswalker, .sorcery, .kindred, .dungeon, .plane, .phenomenon,
  .vanguard, .scheme, .conspiracy
]

def typeOfOracle? (s : String) : Option CardType :=
  let s := lowerAscii s
  let named := fun (name : String) =>
    cardTypes.find? (fun t => lowerAscii t.englishName == name)
  match named s with
  | some t => some t
  | none =>
    if s.endsWith "s" && s.length > 1 then named (s.dropEnd 1).trimAscii.copy else none

def cardSubtypes : List CardSubtype := [
  .adventure, .advisor, .alien, .ape, .arcane, .archer, .army, .artificer,
  .assassin, .aura, .avatar, .barbarian, .bard, .bat, .bear, .beast,
  .berserker, .bird, .cat, .centaur, .citizen, .cleric, .clue, .demigod,
  .detective, .dinosaur, .doctor, .dog, .dragon, .druid, .dwarf, .elder, .elemental,
  .elephant, .elf, .elk, .equipment, .eternal, .food, .forest, .frog, .gamma,
  .gate, .giant, .goblin, .god, .halfling, .hero, .horror, .horse, .human,
  .infinity, .inhuman, .insect, .island, .knight, .kree, .mercenary, .merfolk,
  .minion, .minotaur, .mountain, .mutant, .nightmare, .ninja, .noble, .ogre, .orc,
  .peasant, .performer, .pilot, .pirate, .plains, .plan, .rabbit, .ranger,
  .robot, .rogue, .saga, .samurai, .scientist, .scout, .shaman, .shapeshifter,
  .skrull, .snake, .soldier, .sorcerer, .spider, .spirit, .spy, .squirrel,
  .stone, .swamp, .troll, .treasure, .vampire, .vehicle, .villain, .wall, .warlock,
  .warrior, .whale, .wizard, .wolf, .wraith, .wurm, .zombie
]

def subtypeOfOracle? (s : String) : Option CardSubtype :=
  let s := lowerAscii s
  cardSubtypes.find? (fun st => lowerAscii (toString st) == s)

def partOfTypeWord? (w : String) : Option CardPart :=
  (supertypeOfOracle? w).map CardPart.supertype <|>
    (typeOfOracle? w).map CardPart.type <|>
    (subtypeOfOracle? w).map CardPart.subtype

def isCardTypePart : CardPart → Bool
  | .type _ => true
  | _ => false

/-- A type line such as `Instant — Adventure` or `Legendary Creature — Dwarf Scout`.
Every word must be a supertype, card type, or subtype, and at least one word
must be a card type. Anything else is `none`. -/
def parseTypeLine (line : String) : Option (List CardPart) :=
  let line := stripReminderParenthetical line
  let words := (line.splitOn "—").flatMap fun side =>
    let side := side.trimAscii.copy
    side.splitOn " " |>.filterMap fun w =>
      let w := w.trimAscii.copy
      if w.isEmpty then none else some w
  if words.isEmpty then none
  else
    (words.mapM partOfTypeWord?).bind fun parts =>
      if parts.any isCardTypePart then some parts else none

/-- Split `Concerted Care {1}{W}` into the name and the brace text. -/
def splitNameCost (line : String) : String × String :=
  match line.splitOn "{" with
  | [] => (line.trimAscii.copy, "")
  | name :: rest =>
    if rest.isEmpty then (name.trimAscii.copy, "")
    else (name.trimAscii.copy, "{" ++ String.intercalate "{" rest)

/-- `Concerted Care {1}{W}` as a name and mana cost.
A brace cost that is not mana symbols makes the parse fail. -/
def parseNameAndCost (line : String) : Option (List CardPart) :=
  let line := stripReminderParenthetical line
  let (name, costText) := splitNameCost line
  if name.isEmpty then none
  else if costText.isEmpty then some [.name name]
  else
    match nonemptyMana? costText with
    | some syms => some [.name name, .manaCost syms]
    | none => none

def selectorOfTypes : List CardType → Selector
  | [t] => .cardType t
  | ts => .union (ts.map fun t => .cardType t)

/-- A permanent of `ts`, plus any further constraints. -/
def permanentWith (ts : List CardType) (more : List Selector := []) : Selector :=
  .intersection ([.permanent, selectorOfTypes ts] ++ more)

/-- Controlled by this object's controller (`you control`). -/
def youControl : Selector :=
  .controlled (.controller .this)

/-- `front` and `back` added around `sel`.
An intersection keeps its parts. Anything else becomes one piece of a new
intersection. -/
def extendIntersection (front : List Selector) (sel : Selector) (back : List Selector) :
    Selector :=
  match sel with
  | .intersection parts => .intersection (front ++ parts ++ back)
  | other => .intersection (front ++ [other] ++ back)

/-- `sel` among objects this object's controller controls. -/
def andYouControl (sel : Selector) : Selector :=
  extendIntersection [] sel [youControl]

/-- Equipment this object's controller controls. -/
def equipmentYouControl : Selector :=
  .intersection [.permanent, .subtype .equipment, youControl]

/-- Text before a trailing `you control`, and whether that phrase was present. -/
def splitYouControl (s : String) : String × Bool :=
  match before? s " you control" with
  | some obj => (obj, true)
  | none => (s, false)

/-- Permanent card types joined by `or`, e.g. `artifact or creature`. -/
def typesInPhrase (s : String) : Option (List CardType) :=
  let parts := s.splitOn " or " |>.map (·.trimAscii.copy) |>.filter (· != "")
  if parts.isEmpty then none
  else
    match parts.mapM typeOfOracle? with
    | none => none
    | some ts => if ts.all CardType.isPermanentType then some ts else none

/-- `target artifact or creature you control` as a battlefield selector. -/
def parseTargetPhrase (s : String) : Option Selector :=
  (after? (norm s) "target ").bind fun rest =>
    let (obj, controlled) := splitYouControl rest
    (typesInPhrase obj).map fun ts =>
      permanentWith ts (if controlled then [youControl] else [])

/-- Creature subtypes in `Elf`, `Goblin or Orc`, or `Bear, Spider, or Wolf`. -/
def parseSubtypeList (s : String) : Option (List CardSubtype) :=
  let parts := orList s
  if parts.isEmpty then none else parts.mapM subtypeOfOracle?

/-- One subtype, or a union when several are printed. -/
def subtypeSelector : List CardSubtype → Selector
  | [st] => .subtype st
  | sts => .union (sts.map fun st => .subtype st)

/-- `target creature you control`, `another target creature you control`, or
`target Elf you control`. A creature type is a creature of those subtypes.
`another` excludes this object. -/
def parseBattlefieldTarget (s : String) : Option Selector :=
  let s := norm s
  let opened :=
    match after? s "another target " with
    | some rest => some (true, rest)
    | none =>
      match after? s "target " with
      | some rest => some (false, rest)
      | none => none
  opened.bind fun (another, rest) =>
    let (obj, controlled) := splitYouControl rest
    let head : List Selector :=
      (if another then [.not .this] else []) ++ [.permanent]
    let tail : List Selector := if controlled then [youControl] else []
    match typesInPhrase obj with
    | some ts => some (.intersection (head ++ [selectorOfTypes ts] ++ tail))
    | none =>
      (parseSubtypeList obj).map fun sts =>
        .intersection (head ++ [.cardType .creature, subtypeSelector sts] ++ tail)

/-- Keywords in `hexproof and indestructible` or `haste, flying, and trample`. -/
def parseKeywordPhrase (s : String) : Option (List Keyword) :=
  let commaParts := (norm s).splitOn ", " |>.map copied |>.filter (· != "")
  let tokens := commaParts.flatMap fun part =>
    let part := (after? part "and ").getD part
    part.splitOn " and " |>.map copied |>.filter (· != "")
  if tokens.isEmpty then none else tokens.mapM keywordOfOracle?

/-- Each keyword as an ability gained by `sel`. -/
def keywordGains (sel : Selector) (kws : List Keyword) : List ContinuousEffect :=
  kws.map fun k => .gainAbility sel (.keyword k)

/-- Keywords gained by target `n`. The first keyword declares the target.
Later keywords refer to that same target. -/
def gainEffects (n : Nat) (sel : Selector) (kws : List Keyword) : List ContinuousEffect :=
  match kws with
  | [] => []
  | k :: rest =>
    .gainAbility (.target n sel) (.keyword k) ::
      keywordGains (.targetReference n) rest

def parseSignedInt (s : String) : Option Int :=
  let s := copied s
  let (neg, digits) :=
    match after? s "+" with
    | some d => (false, d)
    | none =>
      match after? s "-" with
      | some d => (true, d)
      | none => (false, s)
  match natOfDigits? digits with
  | none => none
  | some n =>
    let i : Int := n
    some (if neg then -i else i)

/-- A printed power and toughness change, such as `+1/+1`. -/
def parsePowerToughness (s : String) : Option (Int × Int) :=
  match split2? s "/" with
  | some (p, t) =>
    match parseSignedInt p, parseSignedInt t with
    | some p, some t => some (p, t)
    | _, _ => none
  | none => none

/-- `creatures you control` or `other creature you control` as a battlefield
selector. A trailing `s` on a card type is the plural (`creatures`). -/
def parseControlledPhrase (s : String) : Option Selector :=
  let s := norm s
  let (obj0, controlled) := splitYouControl s
  let (obj, other) :=
    match after? obj0 "other " with
    | some obj => (obj, true)
    | none => (obj0, false)
  match typesInPhrase obj with
  | none => none
  | some ts =>
    let head : List Selector :=
      (if other then [.not .this] else []) ++ [.permanent, selectorOfTypes ts]
    let tail : List Selector :=
      if controlled then [youControl] else []
    some (.intersection (head ++ tail))

/-- `it` / `this creature`, or a controlled-permanent phrase. -/
def parsePumpWho (s : String) : Option Selector :=
  match norm s with
  | "it" | "this" | "this creature" => some (.source .this)
  | _ => parseControlledPhrase s

/-- `who gets pt` or `who get pt`. -/
def splitGets? (s : String) : Option (String × String) :=
  split2? s " gets " <|> split2? s " get "

/-- `who gets pt`. The plural `get` is a different printed verb. -/
def splitGetsOnly? (s : String) : Option (String × String) :=
  split2? s " gets "

/-- `+P/+T` and the keywords of an optional `and gains` clause.
No `and gains` is an empty keyword list. An unrecognized keyword fails. -/
def ptAndGains? (s : String) : Option (Int × Int × List Keyword) :=
  let (ptText, kws?) :=
    match split2? s " and gains " with
    | none => (s, some ([] : List Keyword))
    | some (pt, gained) => (pt, parseKeywordPhrase gained)
  match parsePowerToughness ptText, kws? with
  | some (p, t), some kws => some (p, t, kws)
  | _, _ => none

/-- Subject, power, and toughness of `<who> <split> <pt> until end of turn`. -/
def whoPtUntilEnd? (sentence : String)
    (split : String → Option (String × String)) : Option (String × Int × Int) :=
  (before? (normSentence sentence) " until end of turn").bind split |>.bind
    fun (who, ptText) =>
      (parsePowerToughness ptText).map fun (p, t) => (who, p, t)

/-- Text before `until end of turn`, and an optional `for each …` clause.
A sentence that does not end that way fails. -/
def splitUntilEnd? (s : String) : Option (String × Option String) :=
  match split2? s " until end of turn for each " with
  | some (pre, among) =>
    some (pre, if among.isEmpty then none else some among)
  | none =>
    (before? s "until end of turn").map fun body => (body, none)

/-- `+P/+T` as `addPower` and `addToughness`. A zero bonus is omitted.
The first effect declares any targets in `sel`. Later effects use
`targetReference`. `powerValue` and `toughnessValue` build the amounts. -/
def scaledPowerToughness (sel : Selector) (p t : Int)
    (powerValue : Int → Value) (toughnessValue : Int → Value) : List ContinuousEffect :=
  let power :=
    if p == 0 then [] else [.addPower sel (powerValue p)]
  let later := if power.isEmpty then sel else sel.referenceTargets
  let toughness :=
    if t == 0 then [] else [.addToughness later (toughnessValue t)]
  power ++ toughness

/-- `+P/+T` as a flat integer bonus. A zero bonus is omitted. -/
def flatPowerToughness (sel : Selector) (p t : Int) : List ContinuousEffect :=
  scaledPowerToughness sel p t Value.int Value.int

/-- Static `+P/+T` parts. A zero bonus is omitted. `+0/+0` is not an effect. -/
def staticPowerToughness (sel : Selector) (p t : Int) : Option (List CardPart) :=
  let effects := flatPowerToughness sel p t
  if effects.isEmpty then none
  else some (effects.map fun e => .ability (.static e))

/-- `effects` while `cond` holds. No effects is not an ability. -/
def staticWhile (cond : Condition) (effects : List ContinuousEffect) : Option CardPart :=
  if effects.isEmpty then none
  else some (.ability (.static (.if cond effects)))

/-- `+P/+T` until end of turn, optionally once per `among`.
A zero bonus is omitted. `+0/+0` is not an effect. -/
def pumpUntilEnd (sel : Selector) (p t : Int) (among : Option Selector) :
    Option CardAction :=
  let effects :=
    match among with
    | none => flatPowerToughness sel p t
    | some among =>
      scaledPowerToughness sel p t
        (fun n => Value.timesCount n among)
        (fun n => Value.timesCount n (if p == 0 then among else among.referenceTargets))
  if effects.isEmpty then none else some (.continuous effects .endOfTurn)

/-- `+P/+T` on target `n` until end of turn, plus keywords on that same target.
No keywords is only the power and toughness change. An empty change fails. -/
def pumpGainsUntilEnd (n : Nat) (sel : Selector) (p t : Int)
    (kws : List Keyword) : Option (CardAction × Nat) :=
  let effects :=
    flatPowerToughness (.target n sel) p t ++ keywordGains (.targetReference n) kws
  if effects.isEmpty then none
  else some (.continuous effects .endOfTurn, n + 1)

/-- `<objects> get +P/+T until end of turn [for each <objects>].` -/
def parsePumpUntilEndOfTurn (sentence : String) : Option CardAction :=
  (splitUntilEnd? (normSentence sentence)).bind fun (body, among?) =>
    (splitGets? body).bind fun (who, pt) =>
      match parsePumpWho who, parsePowerToughness pt with
      | some sel, some (p, t) =>
        match among? with
        | none => pumpUntilEnd sel p t none
        | some amongText =>
          (parseControlledPhrase amongText).bind fun among =>
            pumpUntilEnd sel p t (some among)
      | _, _ => none

/-- This creature gets +P/+T until end of turn. -/
def sourceGetsUntilEnd? (action : CardAction) : Option (Int × Int) :=
  match action with
  | .continuous effects .endOfTurn => CardAction.leftoverSourcePump? effects
  | _ => none

/-- `lead` then a pump of this creature until end of turn, as `event`.
`accept` chooses which +P/+T is this ability. -/
def triggeredSourcePump (line lead : String) (event : Trigger)
    (accept : Int × Int → Bool) : Option CardPart :=
  (after? line lead).bind parsePumpUntilEndOfTurn |>.bind fun action =>
    (sourceGetsUntilEnd? action).bind fun pt =>
      if accept pt then some (.ability (.triggered event action)) else none

/-- Wrap a parsed effect as a triggered ability. -/
def onTrigger (event : Trigger) (action? : Option CardAction) : Option CardPart :=
  action?.map fun action => .ability (.triggered event action)

/-- Same as `onTrigger`, keeping the target number the effect parser returns. -/
def onTriggerN (event : Trigger) (parsed : Option (CardAction × Nat)) :
    Option (CardPart × Nat) :=
  parsed.map fun (action, n') => (.ability (.triggered event action), n')

/-- The action from a sentence parser, dropping the target number it returns. -/
def actionOf (parsed : Option (CardAction × Nat)) : Option CardAction :=
  parsed.map fun (action, _) => action

/-- `Whenever this creature attacks, it gets +1/+1 until end of turn for each
other creature you control.` -/
def parseAttackTriggered (line : String) : Option CardPart :=
  onTrigger (.attack .this .all)
    ((after? (normLine line) "whenever this creature attacks, ").bind parsePumpUntilEndOfTurn)

/-- `Pay 2 life` (CR 118.3). The amount is a printed number. -/
def parsePayLife (s : String) : Option Nat :=
  (between? (norm s) "pay " " life").bind positiveDigits?

/-- How many +1/+1 counters a printed `a` / `one` / `three` names.
`a` is one counter. Zero is not a count. -/
def counterCount? (s : String) : Option Nat :=
  if norm s == "a" then some 1 else positiveCount s

/-- A printed count that agrees with its noun.
One (`a`, `one`, `1`) takes the singular. Any larger count takes the plural. -/
def nounCount? (countText : String) (plural : Bool) : Option Nat :=
  (counterCount? countText).bind fun n =>
    if (n == 1) == plural then none else some n

/-- Count and object of `put <count> +1/+1 counter(s) on <who>`.
One counter uses the singular noun; more than one uses the plural. -/
def parsePutPlusOneOn? (sentence : String) : Option (Nat × String) :=
  (after? (normSentence sentence) "put ").bind fun rest =>
    let counted :=
      (split2? rest " +1/+1 counters on ").map (fun (c, w) => (c, true, w)) <|>
        (split2? rest " +1/+1 counter on ").map (fun (c, w) => (c, false, w))
    match counted with
    | some (countText, plural, who) =>
      (nounCount? countText plural).map fun k => (k, who)
    | none => none

/-- `Put a +1/+1 counter on this creature` or
`Put three +1/+1 counters on this creature`.
One counter uses the singular noun; more than one uses the plural.
`this`, `this creature`, and `it` are the source of this ability. -/
def parsePutCountersOnThis (sentence : String) : Option CardAction :=
  (parsePutPlusOneOn? sentence).bind fun (k, who) =>
    match parsePumpWho who with
    | some sel =>
      if sel == .source .this then
        some (.putCounter (.source .this) .plusOnePlusOne (.nat k))
      else none
    | none => none

/-- Exile the top card of your library; you may play that card until the end
of your next turn. The exile is action `n`. -/
def exileTopPlayUntilEndOfNextTurn (n : Nat) : CardAction :=
  .sequence [
    .actionId n (.exile (.topOfLibrary (.controller .this) 1)),
    .continuous
      [.canPlay (.controller .this) (.wasCreatedByAction n)]
      (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])]

/-- `Exile the top card of your library. You may play it until the end of your next turn.` -/
def parseExileTopMayPlay (ss : List String) (n : Nat) : Option (CardAction × Nat) :=
  match ss with
  | [exile, play] =>
    if !sentenceIs exile "exile the top card of your library" then none
    else if !sentenceIs play "you may play it until the end of your next turn" then none
    else some (exileTopPlayUntilEndOfNextTurn n, n + 1)
  | _ => none

/-- A printed limit on when an activated ability may be activated (CR 602.5). -/
inductive ActivateLimit where
  | unlimited
  | onceEachTurn
  | duringYourTurn
  | duringYourTurnOnce
  /-- `Activate only as a sorcery` (CR 602.5a). -/
  | asSorcery

/-- `once each turn`, including that limit combined with your turn. -/
def ActivateLimit.limitsOnce : ActivateLimit → Bool
  | .onceEachTurn | .duringYourTurnOnce => true
  | .unlimited | .duringYourTurn | .asSorcery => false

/-- `during your turn`, including that limit combined with once each turn. -/
def ActivateLimit.limitsToYourTurn : ActivateLimit → Bool
  | .duringYourTurn | .duringYourTurnOnce => true
  | .unlimited | .onceEachTurn | .asSorcery => false

def parseActivateLimit (s : String) : ActivateLimit :=
  match normSentence s with
  | "activate only once each turn" => .onceEachTurn
  | "activate only during your turn" => .duringYourTurn
  | "activate only during your turn and only once each turn" => .duringYourTurnOnce
  | "activate only as a sorcery" => .asSorcery
  | _ => .unlimited

/-- Drop a trailing activation limit. A sentence that is not a limit stays
part of the effect. -/
def splitActivateLimit : List String → List String × ActivateLimit
  | [] => ([], .unlimited)
  | [s] =>
    match parseActivateLimit s with
    | .unlimited => ([s], .unlimited)
    | lim => ([], lim)
  | s :: rest =>
    let (body, lim) := splitActivateLimit rest
    (s :: body, lim)

/-- Another permanent of subtype `st` that this object's controller controls. -/
def anotherSubtypeYouControl (st : CardSubtype) : Selector :=
  .intersection [.not .this, .permanent, .subtype st, youControl]

/-- `Sacrifice another creature or artifact`: one other permanent of those
types. `Sacrifice another Goblin`: one other permanent of that subtype you
control. `another` excludes this object. -/
def parseSacrificeAnother (s : String) : Option Cost :=
  match after? (norm s) "sacrifice another " with
  | some obj =>
    match typesInPhrase obj with
    | some ts =>
      some (.sacrificeCount
        (.intersection [.not .this, .permanent, selectorOfTypes ts])
        1)
    | none =>
      (subtypeOfOracle? obj).map fun st =>
        .sacrificeCount (anotherSubtypeYouControl st) 1
  | none => none

/-- `Sacrifice an artifact or creature` as sacrificing one matching permanent. -/
def parseSacrificeAn (s : String) : Option Cost :=
  match (after? (norm s) "sacrifice ").bind dropArticle? with
  | some obj =>
    (typesInPhrase obj).map fun ts => .sacrificeCount (permanentWith ts) 1
  | none => none

/-- `this` or `this <type>`, such as `this creature` or `this spell`. -/
def isGenericSelf (subject : String) : Bool :=
  let s := norm subject
  if s == "this" then true
  else
    match after? s "this " with
    | none => false
    | some rest =>
      if (rest.splitOn " ").length != 1 then false
      else
        (typeOfOracle? rest).isSome || (subtypeOfOracle? rest).isSome ||
          rest == "permanent" || rest == "spell" || rest == "token"

/-- The printed name, the short name before a comma (CR 201.5), and that
name's first word when it is not an article. `Bilbo Baggins, Burglar` refers
to itself as `Bilbo Baggins` or `Bilbo`. `Gollum the Abandoned` refers to
itself as `Gollum`. -/
def selfNames (cardName : String) : List String :=
  let name := norm cardName
  if name.isEmpty then []
  else
    let short :=
      match name.splitOn "," with
      | head :: _ => head.trimAscii.copy
      | [] => name
    let firstWord :=
      match short.splitOn " " with
      | w :: _ => w.trimAscii.copy
      | [] => ""
    let names :=
      if short.isEmpty || short == name then [name] else [name, short]
    if firstWord.isEmpty || firstWord == name || firstWord == short ||
        firstWord == "the" || firstWord == "a" || firstWord == "an" then
      names
    else
      names ++ [firstWord]

/-- `subject` is this card: a generic `this` phrase, or one of `cardName`'s
self-names. -/
def refersToSelf (cardName subject : String) : Bool :=
  isGenericSelf subject || (selfNames cardName).contains (norm subject)

/-- `Sacrifice this land`: sacrifice this object. -/
def parseSacrificeThis (cardName s : String) : Option Cost :=
  (after? (norm s) "sacrifice ").bind fun obj =>
    if refersToSelf cardName obj then some (.sacrifice .this) else none

/-- `Discard a card`: this object's controller discards one card they own
from a hand (CR 701.8). -/
def discardOneCardFromHand : Cost :=
  .discard
    (.selected
      (.controller .this)
      (.range 1 1)
      (.intersection [.inHand, .owner (.controller .this)]))

/-- `Discard a card` as a printed cost. -/
def parseDiscardACard (s : String) : Option Cost :=
  if norm s == "discard a card" then some discardOneCardFromHand else none

/-- One printed cost: mana symbols, the tap symbol, sacrificing a permanent,
or discarding a card. -/
def parsePrintedCost (cardName s : String) : Option Cost :=
  if norm s == "{t}" then some .tapSymbol
  else
    match nonemptyMana? s with
    | some syms => some (.mana syms)
    | none =>
      parseSacrificeThis cardName s <|> parseSacrificeAn s <|>
        parseSacrificeAnother s <|> parseDiscardACard s

/-- Costs separated by commas, such as `{2}{G}{U}, {T}, Sacrifice this land`.
One unrecognized cost fails the list. -/
def parsePrintedCosts (cardName s : String) : Option (List Cost) :=
  let parts := s.splitOn ", " |>.map (·.trimAscii.copy) |>.filter (· != "")
  if parts.isEmpty then none else parts.mapM (parsePrintedCost cardName)

/-- Wrap `action` as an activated ability.
`once each turn` is tracked by ability number `n` (CR 602.5).
`nAfter` is the next number after effects inside `action`.
`Activate only as a sorcery` is `activatedIf` of sorcery timing (CR 602.5a). -/
def activatedWithCost (n : Nat) (costs : List Cost) (action : CardAction)
    (limit : ActivateLimit) (nAfter : Nat) : CardPart × Nat :=
  match limit with
  | .asSorcery =>
    (.ability (.activatedIf (.timeToCastSorcery (.controller .this)) costs action), nAfter)
  | .unlimited | .onceEachTurn | .duringYourTurn | .duringYourTurnOnce =>
    let once := limit.limitsOnce
    let onYourTurn := limit.limitsToYourTurn
    let notYet := Condition.didNotHappen (.abilityWithIdActivated n) .turnStart
    let yourTurn := Condition.turn (.controller .this)
    let cond? : Option Condition :=
      match onYourTurn, once with
      | false, false => none
      | true, false => some yourTurn
      | false, true => some notYet
      | true, true => some (.and yourTurn notYet)
    let ability : Ability :=
      match cond? with
      | none => .activated costs action
      | some cond => .activatedIf cond costs action
    let ability := if once then Ability.abilityId n ability else ability
    let next := if once then max nAfter (n + 1) else nAfter
    (.ability ability, next)

/-- Mana cost, a life payment, sacrificing another permanent, or a
comma-separated list of printed costs (`{2}{G}{U}, {T}, Sacrifice this land`).
An empty brace list fails rather than falling through. Sacrificing a permanent
that is not `another` or `this`, and is not one item of a comma-separated
list, is not an activation cost here. -/
def parseActivationCost (cardName costText : String) : Option (List Cost) :=
  (nonemptyMana? costText).map (fun syms => [.mana syms]) <|>
    (parsePayLife costText).map (fun life => [.life life]) <|>
    (parseSacrificeAnother costText).map (fun c => [c]) <|>
    if (costText.splitOn ", ").length < 2 then none
    else parsePrintedCosts cardName costText

/-- The creature named by a stack cost reduction: `a tapped creature` or
`an attacking nontoken creature`. -/
def costReductionTarget? (s : String) : Option Selector :=
  match norm s with
  | "a tapped creature" =>
    some (.intersection [.permanent, .cardType .creature, .tapped])
  | "an attacking nontoken creature" =>
    some (.intersection [
      .permanent,
      .cardType .creature,
      .attacking .all,
      .not .token])
  | _ => none

/-- Nonempty mana cost in `this spell costs {cost} <mark> <condition>`. -/
def costsLessBy? (s mark : String) : Option (List ManaSymbol × String) :=
  match after? s "this spell costs " with
  | none => none
  | some rest =>
    match split2? rest mark with
    | some (costText, cond) =>
      (nonemptyMana? costText).map fun syms => (syms, cond)
    | none => none

/-- A stack static that reduces this spell's cost when `cond` holds (CR 604.2). -/
def reduceOnStack (cond : Condition) (syms : List ManaSymbol) : CardPart :=
  .ability (.stackStatic (.if cond [.reduceCost .this [.mana syms]]))

/-- `This spell costs {3} less to cast if it targets a tapped creature.`
Also `… an attacking nontoken creature.`
Also `… if a creature died this turn.`
The reduction is a static ability that functions on the stack (CR 604.2). -/
def parseCostReduction (line : String) : Option CardPart :=
  (costsLessBy? (normLine line) " less to cast if ").bind fun (syms, cond) =>
    let cond? : Option Condition :=
      match after? cond "it targets " with
      | some targetText =>
        (costReductionTarget? targetText).map fun among =>
          .targetsIncludeAny .this among
      | none =>
        if cond == "a creature died this turn" then
          some (.happened (.die (.cardType .creature)) .turnStart)
        else none
    cond?.map (reduceOnStack · syms)

/-- Life named by `<lead> N life`, such as `you gain 2 life`. -/
def lifeAmount? (s lead : String) : Option Nat :=
  (between? s lead " life").bind positiveCount

/-- `one`, `two`, or `one or two`. A range is ordered from low to high.
Zero is not a count. -/
def parseCountRange (s : String) : Option Range :=
  match split2? s " or " with
  | some (a, b) =>
    match positiveCount a, positiveCount b with
    | some lo, some hi =>
      if lo <= hi then some (.range (Value.nat lo) (Value.nat hi)) else none
    | _, _ => none
  | none =>
    (positiveCount s).map fun n => .range (Value.nat n) (Value.nat n)

/-- `one, two, or three` as an inclusive contiguous range.
The numbers are positive and listed from low to high with no gaps. -/
def parseContiguousCounts (s : String) : Option (Nat × Nat) :=
  match (orList s).mapM englishSmall? with
  | none => none
  | some ns =>
    match ns with
    | [] => none
    | first :: _ =>
      let lo := ns.foldl (fun a b => Nat.min a b) first
      let hi := ns.foldl (fun a b => Nat.max a b) first
      let expected := (List.range (hi + 1)).filter (fun i => i ≥ lo)
      if ns == expected && lo > 0 then some (lo, hi) else none

/-- `Tap one or two target creatures.` The target number is `n`. -/
def parseTap (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match (after? (normSentence sentence) "tap ").bind (split2? · " target ") with
  | some (countText, obj) =>
    match parseCountRange countText, typesInPhrase obj with
    | some r, some ts =>
      some (.tap (.targets n r (permanentWith ts)), n + 1)
    | _, _ => none
  | none => none

/-- `Untap target <permanents> [you control].` The target number is `n`. -/
def parseUntap (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match (after? (normSentence sentence) "untap ").bind parseTargetPhrase with
  | some sel => some (.untap (.target n sel), n + 1)
  | none => none

/-- `It gets +P/+T until end of turn.` refers to the last target (`n - 1`). -/
def parseItGetsUntilEndOfTurn (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if n <= 1 then none
  else
    (whoPtUntilEnd? sentence splitGetsOnly?).bind fun (who, p, t) =>
      if who != "it" then none
      else
        (pumpUntilEnd (.targetReference (n - 1)) p t none).map fun action =>
          (action, n)

/-- `If it's a Dwarf, you may attach an Equipment you control to it.`
The previous target (`n - 1`) is the host. -/
def parseIfItsSubtypeMayAttach (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if n <= 1 then none
  else
    (between? (normSentence sentence) "if it's " " you control to it").bind
        (split2? · ", you may attach ") |>.bind fun (hostArt, attachArt) =>
      match dropArticle? hostArt, dropArticle? attachArt with
      | some hostName, some attachName =>
        match subtypeOfOracle? hostName, subtypeOfOracle? attachName with
        | some hostSt, some attachSt =>
          let host := Selector.targetReference (n - 1)
          some (
            .if
              (.anySubtype host hostSt)
              [
                .optional (.controller .this)
                  (.attach
                    (.selected
                      (.controller .this)
                      (.range 1 1)
                      (.intersection [
                        .permanent,
                        .subtype attachSt,
                        youControl]))
                    host)
              ],
            n)
        | _, _ => none
      | _, _ => none

/-- Lands this object's controller controls. -/
def landsYouControl : Selector :=
  permanentWith [.land] [youControl]

/-- `This creature's power and toughness are each equal to the number of lands you control.`
A characteristic-defining ability (CR 208.2a / 604.3). Power and toughness are
each a static ability set to the number of lands you control. -/
def powerToughnessEqualLandsAbilities : List Ability := [
  .static (.setPower .this (.count landsYouControl)),
  .static (.setToughness .this (.count landsYouControl))
]

/-- The printed clause after `<this>'s`. -/
def landsCharacteristicSuffix : String :=
  "power and toughness are each equal to the number of lands you control"

def parsePowerToughnessEqualLands (text : String) : Option (List Ability) :=
  if sentenceIs text ("this creature's " ++ landsCharacteristicSuffix) then
    some powerToughnessEqualLandsAbilities
  else none

/-- `a Bear creature in addition to its other types` as that creature subtype. -/
def parseAddedCreatureSubtype (s : String) : Option CardSubtype :=
  (before? (norm s) " creature in addition to its other types").bind dropArticle?
    |>.bind subtypeOfOracle?

/-- `<this> becomes a Bear creature in addition to its other types and gains "…"`.
The subject is this card. No duration is printed, so the effect lasts until
the end of the game (CR 611.2a). The quotation is a static ability this
object gains. -/
def parseBecomeAndGainStatic (cardName : String) (sentence : String) : Option CardAction :=
  (split2? (normSentence sentence) " becomes ").bind fun (subject, rest) =>
    if !refersToSelf cardName subject then none
    else
      (split2? rest " and gains \"").bind fun (become, quoted) =>
        (before? quoted "\"").bind fun abilityText =>
          match parseAddedCreatureSubtype become, parsePowerToughnessEqualLands abilityText with
          | some st, some [power, toughness] =>
            some (.continuous
              [.gainType .this .creature,
                .gainSubtype .this st,
                .gainAbility .this power,
                .gainAbility .this toughness]
              .endOfGame)
          | _, _ => none

/-- `Target creature can't be blocked this turn.` The target is `n`.
The restriction lasts until end of turn. -/
def parseTargetCantBeBlocked (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (before? (normSentence sentence) " can't be blocked this turn").bind fun who =>
    (parseBattlefieldTarget who).map fun sel =>
      (.continuous [.forbid (.block .any (.target n sel))] .endOfTurn, n + 1)

/-- `Put two +1/+1 counters on target Elf you control.`
One counter uses the singular noun. A creature type is a creature of those
subtypes. The target is `n`. -/
def parsePutCountersOnTarget (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (parsePutPlusOneOn? sentence).bind fun (k, who) =>
    match parseBattlefieldTarget who with
    | some sel =>
      -- A creature type (`Elf`, `Goblin or Orc`), not a card type (`creature`).
      if sel.includedSubtypes.isEmpty then none
      else some (.putCounter (.target n sel) .plusOnePlusOne (.nat k), n + 1)
    | none => none

/-- A basic land card in a library. -/
def basicLandInLibrary : Selector :=
  .intersection [.inLibrary, .cardType .land, .supertype .basic]

/-- Search for one card matching `among`, reveal it, and put it into hand.
The found card is variable `n`. -/
def searchRevealToHand (n : Nat) (among : Selector) : CardAction × Nat :=
  (
    .searchLibraryThenShuffle (.controller .this) [
      .defineSelectorVariable n
        (.selected (.controller .this) (.range 1 1) among),
      .reveal (.variable n),
      .returnToHand (.variable n)],
    n + 1)

/-- `Search your library for a basic land card, put it onto the battlefield tapped, then shuffle.`
Does not choose a target, so the target number stays `n`. -/
def parseSearchBasicLandTapped (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence
      "search your library for a basic land card, put it onto the battlefield tapped, then shuffle" then
    some (
      .searchLibraryThenShuffle
        (.controller .this)
        [
          .putOntoBattlefieldInState
            (.selected (.controller .this) (.range 1 1) basicLandInLibrary)
            [.tapped]],
      n)
  else none

/-- `Search your library for up to two basic land cards, reveal them, put one onto the battlefield tapped and the other into your hand, then shuffle.`
Up to two is zero through two (CR 107.1c). The found cards are variable `n`.
One of them enters tapped. Any not put onto the battlefield go to hand. -/
def parseSearchUpToTwoBasics (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence
      "search your library for up to two basic land cards, reveal them, put one onto the battlefield tapped and the other into your hand, then shuffle" then
    some (
      .searchLibraryThenShuffle
        (.controller .this)
        [
          .defineSelectorVariable n
            (.selected (.controller .this) (.range 0 2) basicLandInLibrary),
          .reveal (.variable n),
          .putOntoBattlefieldInState
            (.selected (.controller .this) (.range 1 1) (.variable n))
            [.tapped],
          .returnToHand (.variable n)],
      n + 1)
  else none

/-- `Add one mana of any color.` The player chooses one of the five colors
(CR 106.4). Does not choose a target, so the target number stays `n`. -/
def parseAddOneManaOfAnyColor (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence "add one mana of any color" then
    some (.addManaOfOneColor (.controller .this) ManaSymbol.anyColor 1, n)
  else none

/-- `Destroy target permanent.` The target number is `n`. -/
def parseDestroyTargetPermanent (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence "destroy target permanent" then
    some (.destroy (.target n .permanent), n + 1)
  else none

/-- This creature's power, including the pronouns a card uses for itself. -/
def selfPowerAmount? (s : String) : Option Value :=
  match norm s with
  | "this creature's power" | "its power" | "her power" | "his power" | "their power" =>
    some (.greatestPower (.source .this))
  | _ => none

/-- `Put X +1/+1 counters on <who>`, or `Put X +1/+1 counters on <who>, where X
is this creature's power`. `X` with no where-clause is the value of X
(CR 107.3). A printed natural count stays in `parsePutPlusOneOn?`. -/
def parsePutVariablePlusOne? (sentence : String) : Option (Value × String) :=
  (after? (normSentence sentence) "put ").bind fun rest =>
    let (body, where?) :=
      match split2? rest ", where x is " with
      | some (body, clause) => (body, some clause)
      | none => (rest, none)
    (split2? body " +1/+1 counters on ").bind fun (countText, who) =>
      if norm countText != "x" then none
      else
        match where? with
        | none => some (.x, who)
        | some clause => (selfPowerAmount? clause).map fun v => (v, who)

/-- `Put X +1/+1 counters on <this>`. The counters go on the source. -/
def parsePutXOnSelf (cardName sentence : String) : Option CardAction :=
  (parsePutVariablePlusOne? sentence).bind fun (amount, who) =>
    if refersToSelf cardName (norm who) || norm who == "it" then
      some (.putCounter (.source .this) .plusOnePlusOne amount)
    else none

/-- A pump, counters, a targeted restriction, a library search, becoming a
creature that gains a static ability, adding one mana of any color, destroying
a permanent, or exiling the top card to play later, optionally followed by an
activation limit. -/
def parseActivatedEffect (cardName : String) (effect : String) (n : Nat) :
    Option (CardAction × ActivateLimit × Nat) :=
  let (body, limit) := splitActivateLimit (sentences effect)
  match body with
  | [one] =>
    let targeted :=
      parseTargetCantBeBlocked one n <|>
        parsePutCountersOnTarget one n <|>
        parseSearchBasicLandTapped one n <|>
        parseSearchUpToTwoBasics one n <|>
        parseDestroyTargetPermanent one n
    let plain :=
      (parsePumpUntilEndOfTurn one <|> parsePutCountersOnThis one <|>
          parseBecomeAndGainStatic cardName one <|>
          parsePutXOnSelf cardName one).map (fun action => (action, n)) <|>
        parseAddOneManaOfAnyColor one n
    (targeted <|> plain).map fun (action, n') => (action, limit, n')
  | _ =>
    (parseExileTopMayPlay body n).map fun (action, n') => (action, limit, n')

/-- `{3}{W}: Creatures you control get +1/+1 until end of turn.`
Also `Pay 2 life: This creature gets +2/+2 until end of turn. Activate only once each turn.`
And `Sacrifice another creature or artifact: Exile the top card of your library. You may play it until the end of your next turn. Activate only during your turn and only once each turn.`
And `{5}{G}{G}: This enchantment becomes a Bear creature in addition to its other types and gains "…"`.
And `{1}, {T}: Add one mana of any color.`
And `{7}, {T}, Sacrifice this artifact: Destroy target permanent.`
And `{1}, {T}, Discard a card: Draw a card.` -/
def parseActivatedAbility (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (splitPrintedAbility? line).bind
    fun (costText, effect) =>
      match parseActivatedEffect cardName effect n, parseActivationCost cardName costText with
      | some (action, limit, n'), some costs =>
        some (activatedWithCost n costs action limit n')
      | _, _ => none

/-- `{5}{W}, {T}: Harness The Mind Stone.` Harness this permanent
(CR 701.64). Reminder text, such as “Once harnessed, its ∞ ability is
active,” is not rules text. -/
def parseHarness (cardName line : String) : Option CardPart :=
  (splitPrintedAbility? line).bind fun (costText, effect) =>
    (after? (normSentence effect) "harness ").bind fun who =>
      if !refersToSelf cardName who then none
      else
        (parseActivationCost cardName costText).map fun costs =>
          .ability (.activated costs (.keyword (.source .this) .harness))

/-- Effect of `<word> <this card> <mid> <effect>`.
`word` is `when` or `whenever`. `mid` is the clause boundary, such as
` enters, `. -/
def triggerSelfEffect? (cardName word s mid : String) : Option String :=
  (after? s (word ++ " ")).bind (split2? · mid) |>.bind fun (subject, effect) =>
    if refersToSelf cardName subject then some effect else none

/-- Effect of `when <this card> <mid> <effect>`.
`mid` is the clause boundary, such as ` enters, ` or ` dies, `. -/
def whenSelfEffect? (cardName s mid : String) : Option String :=
  triggerSelfEffect? cardName "when" s mid

/-- `when <this card> <mid> <effect>` as a triggered ability.
`mid` is the clause boundary, such as ` enters, `. -/
def onSelfTrigger (cardName line mid : String) (event : Trigger)
    (effect? : String → Option CardAction) : Option CardPart :=
  onTrigger event ((whenSelfEffect? cardName (normLine line) mid).bind effect?)

/-- Same as `onSelfTrigger`, keeping the target number the effect parser returns. -/
def onSelfTriggerN (cardName line mid : String) (event : Trigger)
    (effect? : String → Option (CardAction × Nat)) : Option (CardPart × Nat) :=
  onTriggerN event ((whenSelfEffect? cardName (normLine line) mid).bind effect?)

/-- `when <this card> enters, <effect>` as an enters-the-battlefield trigger. -/
def onEnter (cardName line : String) (effect? : String → Option CardAction) : Option CardPart :=
  onSelfTrigger cardName line " enters, " (.enter .this) effect?

/-- `when <this card> dies, <effect>` as a dies trigger. -/
def onDies (cardName line : String) (effect? : String → Option CardAction) : Option CardPart :=
  onSelfTrigger cardName line " dies, " (.die .this) effect?

/-- Same as `onEnter`, keeping the target number the effect parser returns. -/
def onEnterN (cardName line : String)
    (effect? : String → Option (CardAction × Nat)) : Option (CardPart × Nat) :=
  onSelfTriggerN cardName line " enters, " (.enter .this) effect?

/-- Same as `onDies`, keeping the target number the effect parser returns. -/
def onDiesN (cardName line : String)
    (effect? : String → Option (CardAction × Nat)) : Option (CardPart × Nat) :=
  onSelfTriggerN cardName line " dies, " (.die .this) effect?

/-- `whenever <this card> attacks, <effect>` as an attack trigger, keeping the
target number the effect parser returns. -/
def onAttackN (cardName line : String)
    (effect? : String → Option (CardAction × Nat)) : Option (CardPart × Nat) :=
  onTriggerN (.attack .this .all)
    ((triggerSelfEffect? cardName "whenever" (normLine line) " attacks, ").bind effect?)

/-- `<this card> deals 5 damage to target creature.` The source must be this
card. The target number is `n`. -/
def parseDealDamage (cardName : String) (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " deals ").bind fun (who, rest) =>
    if !refersToSelf cardName who then none
    else
      (split2? rest " damage to target ").bind fun (amt, obj) =>
        match positiveDigits? amt, typesInPhrase obj with
        | some amount, some ts =>
          some (.dealDamage .this (.target n (permanentWith ts)) (.nat amount), n + 1)
        | _, _ => none

/-- `Target … gains … until end of turn.` The target number is `n`. -/
def parseGainsUntilEndOfTurn (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match (before? (normSentence sentence) "until end of turn").bind (split2? · " gains ") with
  | some (who, gained) =>
    match parseTargetPhrase who, parseKeywordPhrase gained with
    | some sel, some kws =>
      some (.continuous (gainEffects n sel kws) .endOfTurn, n + 1)
    | _, _ => none
  | none => none

/-- `Target creature gets +2/+2 until end of turn.`
Also `Target creature gets +2/+2 and gains lifelink until end of turn.`
The target number is `n`. A gained keyword refers to that same target. -/
def parseTargetGetsUntilEndOfTurn (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (before? (normSentence sentence) " until end of turn").bind splitGetsOnly? |>.bind
    fun (who, rest) =>
      match parseTargetPhrase who, ptAndGains? rest with
      | some sel, some (p, t, kws) => pumpGainsUntilEnd n sel p t kws
      | _, _ => none

/-- `Creatures target player controls get -1 / -1 until end of turn.`
The player is target `n`. `P/T` may be negative. -/
def parseTargetPlayerControlsGet (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (whoPtUntilEnd? sentence splitGets?).bind fun (who, p, t) =>
    ((before? who " target player controls").bind typesInPhrase).bind fun ts =>
      (pumpUntilEnd (permanentWith ts [.controlled (.target n .player)]) p t none).map
        fun action => (action, n + 1)

/-- `there are two or more creature cards in your graveyard`. -/
def graveyardCountCondition? (s : String) : Option Condition :=
  (between? s "there are " " in your graveyard").bind fun rest =>
    (split2? rest " or more ").bind fun (countText, cards) =>
      match positiveCount countText, (before? cards " cards").bind typeOfOracle? with
      | some k, some t =>
        some (.greaterOrEqual
          (.count (.intersection [.inGraveyard, .cardType t, .owner (.controller .this)]))
          (Value.nat k))
      | _, _ => none

/-- `a card`, `one card`, or `two cards` as how many cards are drawn.
One card is singular. More than one is plural. -/
def parseCardCount (s : String) : Option Nat :=
  let s := norm s
  match before? s " cards" with
  | some countText => nounCount? countText true
  | none =>
    match before? s " card" with
    | some countText => nounCount? countText false
    | none => none

/-- `Target player draws two cards and loses 2 life.`
The player is target `n`. -/
def parseTargetPlayerDrawsLosesLife (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  match (between? (normSentence sentence) "target player draws " " life").bind
      (split2? · " and loses ") with
  | some (drawText, lifeText) =>
    match parseCardCount drawText, positiveCount lifeText with
    | some cards, some life =>
      some (
        .sequence [
          .draw (.target n .player) (Value.nat cards),
          .loseLife (.targetReference n) (Value.nat life)],
        n + 1)
    | _, _ => none
  | none => none

/-- `When Bilbo Baggins enters, draw a card.` The subject is this card. -/
def parseEnterDraw (cardName : String) (line : String) : Option CardPart :=
  onEnter cardName line fun effect =>
    (after? effect "draw ").bind parseCardCount |>.map fun k =>
      .draw (.controller .this) (Value.nat k)

/-- `target creature an opponent controls` as the objects a target matches. -/
def parseOppControlledTarget (s : String) : Option Selector :=
  match (between? (norm s) "target " " an opponent controls").bind typesInPhrase with
  | some ts =>
    some (permanentWith ts [.controlled (.opponent (.controller .this))])
  | none => none

/-- `target <permanents> an opponent controls gets P/T until end of turn.`
The target number is `n`. `P/T` may be negative, as in -1 / -1. -/
def parseOppGetsUntilEndOfTurn (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (whoPtUntilEnd? sentence splitGets?).bind fun (who, p, t) =>
    (parseOppControlledTarget who).bind fun sel =>
      (pumpUntilEnd (.target n sel) p t none).map fun action => (action, n + 1)

/-- `When this creature dies, target creature an opponent controls gets -1 / -1 until end of turn.`
The dying object is this card. The target number is `n`. -/
def parseDiesOppGets (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onDiesN cardName line (parseOppGetsUntilEndOfTurn · n)

/-- `put a +1/+1 counter on this creature`. `this`, `this creature`, and `it`
are the source of this ability. -/
def parsePutPlusOneOnThis (sentence : String) : Option CardAction :=
  (after? (normSentence sentence) "put a +1/+1 counter on ").bind fun who =>
    if parsePumpWho who == some (.source .this) then
      some (.putCounter (.source .this) .plusOnePlusOne 1)
    else none

/-- `Whenever you draw your second card each turn, put a +1/+1 counter on this creature.` -/
def parseDrawSecondPlusOne (line : String) : Option CardPart :=
  onTrigger (.ordinal 2 .turnStart (.draw (.controller .this) .all))
    ((after? (normLine line) "whenever you draw your second card each turn, ").bind
      parsePutPlusOneOnThis)

/-- `Whenever you draw a card, put a +1/+1 counter on this creature.` -/
def parseYouDrawPlusOne (line : String) : Option CardPart :=
  onTrigger (.draw (.controller .this) .all)
    ((after? (normLine line) "whenever you draw a card, ").bind parsePutPlusOneOnThis)

/-- `Counter target spell unless its controller pays {4}.`
The target number is `n`. -/
def parseCounterUnlessPays (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match (after? (normSentence sentence) "counter target ").bind
      (split2? · " unless its controller pays ") with
  | some (obj, costText) =>
    if obj != "spell" then none
    else
      match nonemptyMana? costText with
      | some syms =>
        some (
          .preventable
            (.controller (.targetReference n))
            [.mana syms]
            (.counter (.target n .spell)),
          n + 1)
      | none => none
  | none => none

/-- `Draw two cards, then discard a card.` Does not choose a target. -/
def parseDrawThenDiscard (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match split2? (normSentence sentence) ", then discard " with
  | some (drawPart, discardPart) =>
    match (after? drawPart "draw ").bind parseCardCount, parseCardCount discardPart with
    | some d, some c =>
      some (
        .sequence [
          .draw (.controller .this) (Value.nat d),
          .discard (.controller .this) (Value.nat c)],
        n)
    | _, _ => none
  | none => none

/-- If target `id` would die this turn, exile it instead. -/
def exileIfWouldDie (id : Nat) : ContinuousEffect :=
  .replace (.putToGraveyard (.targetReference id)) [.exile .replacingObject]

/-- `Target creature gets -5 / -5 until end of turn. If that creature would die this turn, exile it instead.`
The pump and the replacement both last until end of turn. Dying is being put
into a graveyard from the battlefield; the replacement exiles that object
instead (CR 614.1). The creature is target `n`. -/
def parsePumpExileIfDies (text : String) (n : Nat) : Option (CardAction × Nat) :=
  match sentences text with
  | [pump, exile] =>
    if !sentenceIs exile "if that creature would die this turn, exile it instead" then none
    else
      match parseTargetGetsUntilEndOfTurn pump n with
      | some (.continuous effects .endOfTurn, n') =>
        match ContinuousEffect.addedPT? effects, ContinuousEffect.targetingSelector? effects with
        | some _, some (.target m (.intersection [.permanent, .cardType .creature])) =>
          some (.continuous (effects ++ [exileIfWouldDie m]) .endOfTurn, n')
        | _, _ => none
      | _ => none
  | _ => none

/-- `Target creature you control deals damage equal to its power to target creature an opponent controls.`
The source is target `n`; the recipient is target `n + 1`. -/
def parseDealsDamageEqualToPower (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  match split2? (normSentence sentence) " deals damage equal to its power to " with
  | some (src, dest) =>
    if (before? src " you control").isNone then none
    else
      match parseTargetPhrase src, parseOppControlledTarget dest with
      | some srcSel, some destSel =>
        some (
          .dealDamageEqualToPower
            (.target n srcSel)
            (.target (n + 1) destSel),
          n + 2)
      | _, _ => none
  | none => none

/-- `Put a +1/+1 counter on target creature you control.`
The target is numbered `n`. -/
def parsePutPlusOneOnTarget (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  match after? (normSentence sentence) "put a +1/+1 counter on " with
  | some who =>
    (parseTargetPhrase who).map fun sel =>
      (.putCounter (.target n sel) .plusOnePlusOne 1, n + 1)
  | none => none

/-- `It gains trample and hexproof until end of turn.`
The keywords are gained by the target already numbered `targetId`. -/
def parseItGainsKeywords (sentence : String) (targetId : Nat) : Option CardAction :=
  (between? (normSentence sentence) "it gains " " until end of turn").bind
    fun gained =>
      (parseKeywordPhrase gained).map fun kws =>
        .continuous (keywordGains (.targetReference targetId) kws) .endOfTurn

/-- `Put a +1/+1 counter on target creature you control. It gains trample and hexproof until end of turn.`
The counter and the keywords share target `n`. -/
def parsePutPlusOneThenGains (text : String) (n : Nat) : Option (CardAction × Nat) :=
  match sentences text with
  | [put, gains] =>
    match parsePutPlusOneOnTarget put n, parseItGainsKeywords gains n with
    | some (putAction, n'), some gain =>
      some (.sequence [putAction, gain], n')
    | _, _ => none
  | _ => none

/-- `Destroy target creature`, `Destroy target creature with flying`, or
`Destroy target creature with power 4 or greater.`
The target number is `n`. `with` names one keyword the permanent must have,
or `power N or greater`. `N` is a positive printed number. -/
def parseDestroy (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "destroy target ").bind fun rest =>
    let destroyed (ts : List CardType) (tail : List Selector) : CardAction × Nat :=
      (.destroy (.target n (permanentWith ts tail)), n + 1)
    let withPower :=
      (split2? rest " with power ").bind fun (obj, powerText) =>
        (before? powerText " or greater").bind positiveCount |>.bind fun p =>
          (typesInPhrase obj).map fun ts =>
            destroyed ts [.powerAtLeast (Value.int (p : Int))]
    let withKeyword :=
      (split2? rest " with ").bind fun (obj, kwText) =>
        (keywordOfOracle? kwText).bind fun k =>
          (typesInPhrase obj).map fun ts => destroyed ts [.keyword k]
    let plain :=
      (typesInPhrase rest).map fun ts => destroyed ts []
    withPower <|> withKeyword <|> plain

/-- `Destroy target artifact or enchantment. You gain 2 life.`
The destroy chooses target `n`. Gaining life does not. `N` is a positive count. -/
def parseDestroyThenGainLife (text : String) (n : Nat) : Option (CardAction × Nat) :=
  match sentences text with
  | [destroy, gain] =>
    match parseDestroy destroy n, lifeAmount? (normSentence gain) "you gain " with
    | some (destroyed, n'), some k =>
      some (.sequence [destroyed, .gainLife (.controller .this) (Value.nat k)], n')
    | _, _ => none
  | _ => none

/-- `Until end of turn, target creature becomes an artifact in addition to its
other types and gains indestructible.`
The target is `n`. The type and indestructible both last until end of turn.
A reminder parenthetical is not rules text (CR 207.2). -/
def parseBecomeArtifactIndestructible (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (after? (normLine sentence) "until end of turn, ").bind fun rest =>
    (split2? rest " becomes ").bind fun (who, become) =>
      (split2? become " and gains ").bind fun (typeText, gained) =>
        if typeText != "an artifact in addition to its other types" then none
        else
          match parseTargetPhrase who, parseKeywordPhrase gained with
          | some sel, some [.indestructible] =>
            if sel != permanentWith [.creature] then none
            else
              some (
                .continuous
                  [.gainType (.target n sel) .artifact,
                    .gainAbility (.targetReference n) (.keyword .indestructible)]
                .endOfTurn,
                n + 1)
          | _, _ => none

/-- Target artifact token, with no further restriction. -/
def artifactTokenPermanent : Selector :=
  .intersection [.permanent, .cardType .artifact, .token]

/-- `Destroy target artifact token.` The token is target `n`. -/
def parseDestroyArtifactToken (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence "destroy target artifact token" then
    some (.destroy (.target n artifactTokenPermanent), n + 1)
  else none

/-- `<this card> deals 3 damage to target creature. If that creature would die this turn, exile it instead.`
The creature is target `n`. Dying this turn is replaced by exile. -/
def parseDealDamageExileIfDies (cardName : String) (text : String) (n : Nat) :
    Option (CardAction × Nat) :=
  match sentences text with
  | [damage, exile] =>
    if !sentenceIs exile "if that creature would die this turn, exile it instead" then none
    else
      match parseDealDamage cardName damage n with
      | some (.dealDamage src (.target id among) amount, n') =>
        if src == .this && among == permanentWith [.creature] then
          some (
            .sequence [
              .dealDamage src (.target id among) amount,
              .continuous [exileIfWouldDie id] .endOfTurn],
            n')
        else none
      | _ => none
  | _ => none

/-- `Tap target creature an opponent controls.` The creature is target `n`. -/
def parseTapOppCreature (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match after? (normSentence sentence) "tap " with
  | some rest =>
    (parseOppControlledTarget rest).map fun sel =>
      (.tap (.target n sel), n + 1)
  | none => none

/-- One printed mode of a “Choose one” spell. The first success wins. -/
def parseModeAction (cardName : String) (text : String) (n : Nat) :
    Option (CardAction × Nat) :=
  parseDealDamageExileIfDies cardName text n <|>
    parseDestroyArtifactToken text n <|>
    parseCounterUnlessPays text n <|>
    parseDrawThenDiscard text n <|>
    parsePumpExileIfDies text n <|>
    parseTargetPlayerDrawsLosesLife text n <|>
    parseTargetGetsUntilEndOfTurn text n <|>
    parseTargetPlayerControlsGet text n <|>
    parseDestroyThenGainLife text n <|>
    parseBecomeArtifactIndestructible text n <|>
    parseDestroy text n <|>
    parsePutPlusOneThenGains text n <|>
    (parsePumpUntilEndOfTurn text).map (·, n) <|>
    parseTapOppCreature text n <|>
    parseUntap text n

/-- The text of a `•` mode line, without the bullet. -/
def stripModeBullet (line : String) : Option String :=
  after? (copied line) "•"

/-- `Choose one —` or `Choose one or both —` (CR 700.2).
`true` means one or both. -/
def chooseHeader? (line : String) : Option Bool :=
  if normLine line == "choose one —" then some false
  else if normLine line == "choose one or both —" then some true
  else none

/-- Parts for a modal spell with at least one parsed mode.
`orBoth` is “choose one or both”: the controller selects one or two distinct
modes. “Choose one” selects exactly one. Each mode is chosen at most once
(CR 700.2). No modes makes the parse fail rather than dropping the printed choice. -/
def chooseOneParts (modes : List CardAction) (orBoth : Bool) : Option (List CardPart) :=
  match modes with
  | [] => none
  | modes =>
    some [.actions [
      if orBoth then
        .chooseUniqueModes (.range 1 2) modes
      else
        .chooseUniqueModes (.range 1 1) modes]]

/-- `<subject> <tail>` as a static restriction, when `subject` is this card. -/
def staticCant (cardName line tail : String) (restriction : Trigger) : Option CardPart :=
  (before? (normLine line) tail).bind fun subject =>
    if subject.isEmpty || !refersToSelf cardName subject then none
    else some (.ability (.static (.forbid restriction)))

/-- `<this card> can't be blocked by tokens.` The subject must be this card. -/
def parseCantBeBlockedByTokens (cardName : String) (line : String) : Option CardPart :=
  staticCant cardName line " can't be blocked by tokens" (.block .token .this)

/-- `<this card> can't be blocked.` The subject must be this card. -/
def parseCantBeBlocked (cardName : String) (line : String) : Option CardPart :=
  staticCant cardName line " can't be blocked" (.block .any .this)

/-- `<this card> can't be blocked by creatures with power 2 or less.`
The subject must be this card. `N` is a positive printed power. -/
def parseCantBeBlockedByPower (cardName : String) (line : String) : Option CardPart :=
  (split2? (normLine line) " can't be blocked by creatures with power ").bind
    fun (subject, rest) =>
      if !refersToSelf cardName subject then none
      else
        (before? rest " or less").bind positiveCount |>.map fun p =>
          .ability (.static (.forbid (.block
            (.intersection [
              .permanent,
              .cardType .creature,
              .powerAtMost (Value.int (p : Int))])
            .this)))

/-- `<this card> can't block.` The subject must be this card. This functions
on the battlefield (CR 604.2 / 509.1b), so it is `static`. -/
def parseCantBlock (cardName : String) (line : String) : Option CardPart :=
  staticCant cardName line " can't block" (.block .this .any)

/-- `Whenever <this card> deals combat damage to a player, draw a card, then
discard a card.` The subject must be this card. The effect is the same
draw-then-discard grammar as a modal spell. -/
def parseCombatDamageLoot (cardName : String) (line : String) : Option CardPart :=
  onTrigger (.combatDamage .this .player)
    ((triggerSelfEffect? cardName "whenever" (normLine line)
        " deals combat damage to a player, ").bind fun effect =>
      actionOf (parseDrawThenDiscard effect 1))

/-- `Exchange control of two target nonland permanents that share a card type.`
The target number is `n`. The noun stays plural, as in the printed template
for a set of permanents. -/
def parseExchangeControlSharingCardType (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  match (between? (normSentence sentence)
      "exchange control of " " that share a card type").bind
      (split2? · " target ") with
  | some (countText, obj) =>
    if obj != "nonland permanents" then none
    else
      match parseCountRange countText with
      | some r =>
        if r == .range 1 1 then none
        else
          some (
            .exchangeControl
              (.targetSet
                n
                r
                (.intersection [.permanent, .not .land])
                [.shareCardType]),
            n + 1)
      | none => none
  | none => none

/-- `Target creature's owner puts it on their choice of the top or bottom of their library.`
The target number is `n`. That creature's owner chooses which library position. -/
def parseOwnerPutsTopOrBottom (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match (between? (normSentence sentence) "target "
      "'s owner puts it on their choice of the top or bottom of their library").bind
      typesInPhrase with
  | some ts =>
    let sel := permanentWith ts
    some (
      .playerSelectAction
        (.owner (.targetReference n))
        (.range 1 1)
        [.putOnTopOfLibrary (.target n sel),
          .putOnBottomOfLibrary (.targetReference n)],
      n + 1)
  | none => none

/-- `Put a +1/+1 counter on up to one target creature.`
Up to one target is zero or one (CR 115.1). The targets are numbered `n`. -/
def parsePutPlusOneUpToOne (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match (after? (normSentence sentence) "put a +1/+1 counter on up to one target ").bind
      typesInPhrase with
  | some ts =>
    some (
      .putCounter
        (.targets n (.range 0 1) (permanentWith ts))
        .plusOnePlusOne
        1,
      n + 1)
  | none => none

/-- `Target player gains 2 life.` The player is target `n`. -/
def parseTargetPlayerGainsLife (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (lifeAmount? (normSentence sentence) "target player gains ").map fun k =>
    (.gainLife (.target n .player) (Value.nat k), n + 1)

/-- `You gain 2 life.` Does not choose a target, so the target number stays `n`. -/
def parseYouGainLife (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (lifeAmount? (normSentence sentence) "you gain ").map fun k =>
    (.gainLife (.controller .this) (Value.nat k), n)

/-- `Scry 2.` Does not choose a target, so the target number stays `n`. -/
def parseScry (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match after? (normSentence sentence) "scry " with
  | some count =>
    (positiveCount count).map fun k => (.scry (.controller .this) (Value.nat k), n)
  | none => none

/-- `Whenever one or more other creatures die, scry 1.`
Those creatures die together, so this is one trigger (CR 603.2c).
The effect is `Scry N`. -/
def parseOtherCreaturesDieScry (line : String) (n : Nat) : Option (CardPart × Nat) :=
  (after? (normLine line) "whenever one or more ").bind (split2? · " die, ") |>.bind
    fun (who, effect) =>
      if who != "other creatures" then none
      else
        (parseControlledPhrase who).bind fun among =>
          onTriggerN (.dieSimultaneously among []) (parseScry effect n)

/-- `Counter target spell. If a permanent spell is countered this way, exile
it instead of putting it into its owner's graveyard. You may cast that card
without paying its mana cost for as long as it remains exiled.`
The counter and its target are numbered `n`. The exile that replaces the
graveyard is `n + 1`, and the free cast refers to that exiled card. -/
def parseCounterExilePermanentMayCast (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [counter, exile, cast] =>
    if !sentenceIs counter "counter target spell" then none
    else if !sentenceIs exile
        "if a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard" then
      none
    else if !sentenceIs cast
        "you may cast that card without paying its mana cost for as long as it remains exiled" then
      none
    else
      let exileId := n + 1
      some (
        [
          .actionId n (.counter (.target n .spell)),
          .continuous
            [.replace
              (.putToGraveyard
                (.intersection [.wasObjectOfAction n, .permanentSpell]))
              [
                .actionId exileId (.exile (.replacingObject)),
                .continuous
                  [.canCastWithoutPayingManaCost
                    (.controller .this)
                    (.wasCreatedByAction exileId)]
                  .endOfGame
              ]]
            .endOfGame
        ],
        exileId)
  | _ => none

/-- `If that spell's mana value was 2 or less, recruit.`
`N` is a positive printed number. Recruit is the effect of that check. -/
def recruitIfSpellMvAtMost? (sentence : String) : Option Nat :=
  (between? (normSentence sentence)
      "if that spell's mana value was " " or less, recruit").bind positiveCount

/-- `Counter target spell. If that spell's mana value was N or less, recruit.`
The spell is target `n`. Before it is countered, value variable `n` records
the greatest mana value of that target, which on the stack includes the
chosen `{X}` (CR 202.3e). Recruit happens only when that variable is less
than or equal to `N`. -/
def parseCounterThenRecruitIfMv (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [counter, cond] =>
    if !sentenceIs counter "counter target spell" then none
    else
      (recruitIfSpellMvAtMost? cond).map fun k =>
        ([
          .defineValueVariable n (.greatestManaValue (.target n .spell)),
          .counter (.targetReference n),
          .if (.lessOrEqual (.variable n) (.nat k))
            [.keyword (.controller .this) .recruit]
        ], n + 1)
  | _ => none

/-- `You may play an additional land this turn.` One extra land play, until end of turn
(CR 305.2b). -/
def parseAdditionalLand (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence "you may play an additional land this turn" then
    some (
      .continuous
        [.increaseLandPlayLimit (.controller .this) (Value.nat 1)]
        .endOfTurn,
      n)
  else none

/-- `You draw a card and lose 1 life.` One card and 1 life. -/
def parseYouDrawCardLoseLife (sentence : String) : Option CardAction :=
  match (after? (normSentence sentence) "you draw ").bind (split2? · " and lose ") with
  | some (drawText, lifeText) =>
    match parseCardCount drawText, lifeAmount? ("lose " ++ lifeText) "lose " with
    | some 1, some 1 =>
      some (.sequence [
        .draw (.controller .this) 1,
        .loseLife (.controller .this) 1])
    | _, _ => none
  | none => none

/-- The subtype printed in `amass Goblins`: the plural drops a trailing `s`. -/
def amassSubtype? (s : String) : Option CardSubtype :=
  if s.endsWith "s" && s.length > 1 then subtypeOfOracle? (s.dropEnd 1).copy else none

/-- `Draw a card.` / `Draw two cards.` The player is this spell's controller.
One card is singular. More than one is plural. -/
def parseDrawCards (sentence : String) : Option CardAction :=
  (after? (normSentence sentence) "draw ").bind parseCardCount |>.map fun k =>
    .draw (.controller .this) (Value.nat k)

/-- `Amass Goblins 1.` The controller amasses that subtype that many (CR 701.45).
The subtype is plural. `N` is a positive count. `Amass Goblins X, where X is
this creature's power` uses that power. -/
def parseAmass (sentence : String) : Option CardAction :=
  (after? (normSentence sentence) "amass ").bind fun rest =>
    match rest.splitOn " " |>.map copied |>.filter (· != "") with
    | typeText :: nWords =>
      let nText := " ".intercalate nWords
      (amassSubtype? typeText).bind fun st =>
        let amount :=
          (positiveCount nText).map Value.nat <|>
            ((after? nText "x, where x is ").bind selfPowerAmount?)
        amount.map fun v => .keyword (.controller .this) (.amass st v)
    | [] => none

/-- `Return up to one target creature card from your graveyard to your hand.`
Up to one target is zero or one (CR 115.1). That card is in your graveyard.
The target is numbered `n`. -/
def parseReturnUpToOneFromYourGraveyard (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (between? (normSentence sentence)
      "return up to one target " " from your graveyard to your hand").bind
    fun obj =>
      (before? obj " card").bind typeOfOracle? |>.map fun t =>
        (.returnToHand
          (.targets n (.range 0 1)
            (.intersection [
              .inGraveyard,
              .cardType t,
              .owner (.controller .this)])),
         n + 1)

/-- `Search your library for a legendary creature card, reveal it, put it into your hand, then shuffle.`
The found card is variable `n`. A legendary creature card, with no further
subtype. -/
def parseSearchLegendaryCreatureToHand (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  if sentenceIs sentence
      "search your library for a legendary creature card, reveal it, put it into your hand, then shuffle" then
    some (searchRevealToHand n
      (.intersection [.inLibrary, .cardType .creature, .supertype .legendary]))
  else none

/-- A parsed action that does not choose a new target. -/
def unchanged (parsed : Option CardAction) (n : Nat) : Option (CardAction × Nat) :=
  parsed.map (·, n)

/-- An instant or a sorcery. -/
def instantOrSorcery : Selector :=
  .union [.cardType .instant, .cardType .sorcery]

/-- Instant and sorcery cards among the objects of action `id`. -/
def instantOrSorceryAmong (id : Nat) : Selector :=
  .intersection [.wasObjectOfAction id, instantOrSorcery]

/-- Mill `k` cards as action `n`, then `put` those cards. -/
def millThen (n k : Nat) (put : Nat → CardAction) : CardAction × Nat :=
  (
    .sequence [
      .actionId n (.mill (.controller .this) (.nat k)),
      put n],
    n + 1)

/-- A plural mill count in `mill <count><tail>`. One card is not this count. -/
def millPluralCount? (sentence tail : String) : Option Nat :=
  (after? (normSentence sentence) "mill ").bind (before? · tail) |>.bind
    (nounCount? · true)

/-- `Mill four cards, then put an instant or sorcery card from among them into your hand.`
More than one card uses the plural `cards`. The milled cards are action `n`.
One instant or sorcery card from among them goes to hand. -/
def parseMillThenPutInstantOrSorcery (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (millPluralCount? sentence
      " cards, then put an instant or sorcery card from among them into your hand").map
    fun k =>
      millThen n k fun id =>
        .returnToHand
          (.selected (.controller .this) (.range 1 1) (instantOrSorceryAmong id))

/-- `Mill six cards, then put all instant and sorcery cards from among them into your hand.`
More than one card uses the plural `cards`. Every instant and sorcery card
from among them goes to hand. The milled cards are action `n`. -/
def parseMillThenPutAllInstantsOrSorceries (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (millPluralCount? sentence
      " cards, then put all instant and sorcery cards from among them into your hand").map
    fun k => millThen n k fun id => .returnToHand (instantOrSorceryAmong id)

/-- `Mill four cards, then put all Elf cards from among them into your hand.`
More than one card uses the plural `cards`. The subtype is printed singular
(`Elf`, not `Elves`). Every card of that subtype from among them goes to
hand. The milled cards are action `n`. -/
def parseMillThenPutAllSubtype (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (after? (normSentence sentence) "mill ").bind fun rest =>
    (split2? rest " cards, then put all ").bind fun (countText, tail) =>
      (nounCount? countText true).bind fun k =>
        ((before? tail " cards from among them into your hand").bind
            subtypeOfOracle?).map fun st =>
          millThen n k fun id =>
            .returnToHand
              (.intersection [.wasObjectOfAction id, .subtype st])

/-- Two creatures and/or lands this object's controller controls. -/
def twoCreaturesOrLandsYouControl : Selector :=
  permanentWith [.creature, .land] [youControl]

/-- `Exile two target creatures and/or lands you control, then return them to the battlefield under their owner's control.`
Those two permanents are target `n`, and that exile is action `n`.
They return under their owner's control. -/
def parseExileTwoThenReturn (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  if sentenceIs sentence
      "exile two target creatures and/or lands you control, then return them to the battlefield under their owner's control" then
    some (
      .sequence [
        .actionId n
          (.exile (.targets n (.range 2 2) twoCreaturesOrLandsYouControl)),
        .putOntoBattlefieldInState
          (.wasCreatedByAction n)
          [.controlled (.owner (.wasCreatedByAction n))]],
      n + 1)
  else none

/-- `Mill four cards, then put up to two land cards from among them into your hand.`
More than one milled card uses the plural `cards`. Up to one land card is
singular; more than one is plural. The milled cards are action `n`. -/
def parseMillThenPutUpToLands (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (after? (normSentence sentence) "mill ").bind fun rest =>
    (split2? rest " cards, then put up to ").bind fun (countText, tail) =>
      (nounCount? countText true).bind fun k =>
        let landTail :=
          (before? tail " land cards from among them into your hand").map
            (true, ·) <|>
          (before? tail " land card from among them into your hand").map
            (false, ·)
        match landTail with
        | some (plural, maxText) =>
          (nounCount? maxText plural).map fun max =>
            millThen n k fun id =>
              .returnToHand
                (.selected
                  (.controller .this)
                  (.range (Value.nat 0) (Value.nat max))
                  (.intersection [.wasObjectOfAction id, .cardType .land]))
        | none => none

/-- `Mill two cards.` More than one card uses the plural `cards`. -/
def parseMillCards (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (millPluralCount? sentence " cards").map fun k => (.mill (.controller .this) (.nat k), n)

/-- Each creature an opponent of this object's controller controls. -/
def eachOppCreature : Selector :=
  .intersection [
    .permanent,
    .cardType .creature,
    .controlled (.opponent (.controller .this))]

/-- Each creature that is not a Dragon. -/
def eachNonDragonCreature : Selector :=
  .intersection [
    .permanent, .cardType .creature, .not (.subtype .dragon)]

/-- `<this card> deals 1 damage to each creature your opponents control.`
Also `… to each non-Dragon creature.` The source is this card. -/
def parseDealDamageToEach (cardName : String) (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " deals ").bind fun (who, rest) =>
    if !refersToSelf cardName who then none
    else
      (split2? rest " damage to each ").bind fun (amt, obj) =>
        (positiveCount amt).bind fun amount =>
          let (obj, opponents) :=
            match before? obj " and each opponent" with
            | some rest => (rest, true)
            | none => (obj, false)
          let dest :=
            if obj == "creature your opponents control" then some eachOppCreature
            else if obj == "non-dragon creature" then some eachNonDragonCreature
            else if obj == "creature" then some (.intersection [.permanent, .cardType .creature])
            else
              (between? obj "non-" " creature").bind subtypeOfOracle? |>.map fun st =>
                .intersection [.permanent, .cardType .creature, .not (.subtype st)]
          dest.map fun sel =>
            if opponents then
              (.sequence [.dealDamage .this sel (.nat amount),
                .dealDamage .this (.opponent (.controller .this)) (.nat amount)], n)
            else (.dealDamage .this sel (.nat amount), n)

/-- One sentence. The first parser that accepts it wins. -/
def parseSentence (cardName sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  parseGainsUntilEndOfTurn sentence n <|>
    parseTap sentence n <|>
    parseUntap sentence n <|>
    parseItGetsUntilEndOfTurn sentence n <|>
    parseIfItsSubtypeMayAttach sentence n <|>
    parseDealDamage cardName sentence n <|>
    parseDealDamageToEach cardName sentence n <|>
    parseDestroyArtifactToken sentence n <|>
    parseDealsDamageEqualToPower sentence n <|>
    parseDestroy sentence n <|>
    parsePutPlusOneUpToOne sentence n <|>
    parseTargetPlayerGainsLife sentence n <|>
    parseYouGainLife sentence n <|>
    unchanged (parseYouDrawCardLoseLife sentence) n <|>
    unchanged (parseAmass sentence) n <|>
    parseReturnUpToOneFromYourGraveyard sentence n <|>
    parseAdditionalLand sentence n <|>
    parseScry sentence n <|>
    parseOwnerPutsTopOrBottom sentence n <|>
    parseExchangeControlSharingCardType sentence n <|>
    parseTargetGetsUntilEndOfTurn sentence n <|>
    parseTargetPlayerControlsGet sentence n <|>
    parseTargetPlayerDrawsLosesLife sentence n <|>
    parseSearchLegendaryCreatureToHand sentence n <|>
    parseMillThenPutAllInstantsOrSorceries sentence n <|>
    parseMillThenPutInstantOrSorcery sentence n <|>
    parseMillThenPutUpToLands sentence n <|>
    parseMillThenPutAllSubtype sentence n <|>
    parseMillCards sentence n <|>
    parseExileTwoThenReturn sentence n

/-- Creatures you control other than target `n`. -/
def eachOtherCreatureThanTarget (n : Nat) : Selector :=
  .intersection [
    .not (.targetReference n),
    .permanent,
    .cardType .creature,
    youControl]

/-- `If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control.`
The extra counter is on every creature you control except target `n`. -/
def parseAlsoPlusOneEachOther (sentence : String) (n : Nat) : Option CardAction :=
  (after? (normSentence sentence)
      "if this spell was cast from a graveyard, also put ").bind fun rest =>
    (split2? rest " +1/+1 counter on each ").bind fun (countText, who) =>
      match nounCount? countText false, who with
      | some 1, "other creature you control" =>
        some (.putCounter (eachOtherCreatureThanTarget n) .plusOnePlusOne 1)
      | _, _ => none

/-- `Put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control.`
The creature is target `n`. The extra counters happen only when this spell
was cast from a graveyard. That cast is an event since the start of the game. -/
def parsePlusOneThenEachOtherIfFromGy (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [put, also] =>
    match parsePutPlusOneOnTarget put n, parseAlsoPlusOneEachOther also n with
    | some (putAction, n'), some alsoAction =>
      some ([
        putAction,
        .if (.happened (.castSpellFromGraveyard .this) .gameStart) [alsoAction]
      ], n')
    | _, _ => none
  | _ => none

/-- The effect after `If this spell was cast from a graveyard, `, without
the trailing `instead`. -/
def fromGraveyardInstead? (sentence : String) : Option String :=
  (after? (normSentence sentence) "if this spell was cast from a graveyard, ").bind
    fun rest => before? rest " instead"

/-- Draw, or amass, and the same action with a different count when this
spell was cast from a graveyard. Both amass the same subtype. The
cast-from-graveyard action is the “instead” branch. -/
def insteadFromGraveyardPair (normal instead : String) :
    Option (CardAction × CardAction) :=
  let drawPair :=
    match parseDrawCards normal, (fromGraveyardInstead? instead).bind parseDrawCards with
    | some normalA, some fromGyA => some (fromGyA, normalA)
    | _, _ => none
  let amassPair :=
    match parseAmass normal, (fromGraveyardInstead? instead).bind parseAmass with
    | some (.keyword who (.amass st na)), some (.keyword who' (.amass st' ga)) =>
      if who == who' && st == st' then
        some (.keyword who (.amass st ga), .keyword who (.amass st na))
      else none
    | _, _ => none
  drawPair <|> amassPair

/-- `Draw a card. If this spell was cast from a graveyard, draw two cards instead.`
Also the same shape for amass. The second sentence replaces the first when
this spell was cast from a graveyard. -/
def parseInsteadFromGraveyard (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [normal, instead] =>
    (insteadFromGraveyardPair normal instead).map fun (fromGyA, normalA) =>
      ([.ifElse
          (.happened (.castSpellFromGraveyard .this) .gameStart)
          [fromGyA]
          [normalA]],
        n)
  | _ => none

/-- `Put two +1/+1 counters on target creature you control.`
The creature is target `n`. A creature type is a different ability. -/
def parsePutPlusOneOnCreatureYouControl (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (parsePutPlusOneOn? sentence).bind fun (k, who) =>
    match parseTargetPhrase who with
    | some sel =>
      if sel == permanentWith [.creature] [youControl] then
        some (.putCounter (.target n sel) .plusOnePlusOne (.nat k), n + 1)
      else none
    | none => none

/-- `Put two +1/+1 counters on target creature you control. Then it fights target creature an opponent controls.`
The creature you control is target `n`. The opponent's creature is the next
target. -/
def parsePlusOneThenFight (text : String) (n : Nat) : Option (List CardAction × Nat) :=
  match sentences text with
  | [put, fights] =>
    match parsePutPlusOneOnCreatureYouControl put n,
        (after? (normSentence fights) "then it fights ").bind parseOppControlledTarget with
    | some (putAction, n'), some dest =>
      some ([putAction, .fight (.targetReference n) (.target n' dest)], n' + 1)
    | _, _ => none
  | _ => none

/-- `Add four mana in any combination of colors. Spend this mana only to cast Dragon spells.`
The mana is one addition in any combination of colors, not that much mana
of one color. That mana can be spent only to cast a spell of the printed
subtype. The addition is action `n`. -/
def parseAddManaCombination (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [add, spend] =>
    (between? (normSentence add) "add " " mana in any combination of colors").bind
      fun countText =>
        if !countText.isEmpty && (split2? countText " ").isSome then none
        else
          (positiveCount countText).bind fun k =>
            (between? (normSentence spend) "spend this mana only to cast " " spells").bind
              subtypeOfOracle? |>.map fun st =>
                ([
                  .actionId n
                    (.addManaInAnyCombination
                      (.controller .this) ManaSymbol.anyColor (.nat k)),
                  .continuous
                    [.forbid
                      (.spendManaCreatedByAction n
                        (.not (.castSpell (.subtype st))))]
                    .endOfTurn],
                  n + 1)
  | _ => none

/-- How many cards `<count> card(s)` names.
One takes the singular. Any larger count takes the plural. -/
def topCount? (phrase : String) : Option Nat :=
  parseCardCount phrase

/-- `Exile all attacking creatures target player controls. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle.`
The player is target `n`, and the exile is action `n`. “That many” is how
many of those creatures are exiled. That player chooses whether to search,
and may find any number from zero up to that many (CR 701.19b). -/
def parseExileAttackersSearchBasics (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [exile, search] =>
    if !sentenceIs exile
        "exile all attacking creatures target player controls" then none
    else if !sentenceIs search
        "that player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle" then
      none
    else
      let exiled := .count (.wasObjectOfAction n)
      some ([
        .actionId n
          (.exile
            (.intersection [
              .permanent,
              .cardType .creature,
              .attacking .all,
              .controlled (.target n .player)])),
        .optional (.targetReference n)
          (.searchLibraryThenShuffle
            (.targetReference n)
            [
              .putOntoBattlefieldInState
                (.selected
                  (.targetReference n)
                  (.range (.nat 0) exiled)
                  (.intersection [
                    .inLibrary,
                    .cardType .land,
                    .supertype .basic]))
                [.tapped]])],
        n + 1)
  | _ => none

/-- `Look at the top two cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a Wizard.`
The looked-at cards are action `n`. The exile is action `n + 1`. One card
uses the singular. Those cards are exiled face down. You may play them
while they remain exiled and you control a permanent of that subtype. -/
def parseLookAtTopExileFaceDownPlayIf (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [look, play] =>
    (after? (normSentence look) "look at the top ").bind fun tail =>
      (before? tail " of your library and exile them face down").bind topCount? |>.bind
        fun k =>
          (after? (normSentence play)
              "for as long as they remain exiled, you may play them if you control ").bind
            dropArticle? |>.bind subtypeOfOracle? |>.map fun st =>
              let exileId := n + 1
              ([
                .actionId n
                  (.lookAt (.topOfLibrary (.controller .this) (.nat k))),
                .actionId exileId
                  (.exileFaceDown (.wasObjectOfAction n)),
                .continuous
                  [.if
                    (.any
                      (.intersection [
                        .permanent,
                        .subtype st,
                        youControl]))
                    [.canPlay
                      (.controller .this)
                      (.intersection [
                        .inExile,
                        .wasCreatedByAction exileId])]]
                  .endOfGame],
                exileId + 1)
  | _ => none

/-- Vision Quest: the player chooses to search the library and graveyard, or
only the graveyard, for an artifact creature of mana value X or less. The
found card is variable `n`. It enters with X +1/+1 counters and gains haste
when X is 4 or greater. Searching the library shuffles. -/
def parseVisionQuest (text : String) (n : Nat) : Option (List CardAction × Nat) :=
  match (sentences text).map normSentence with
  | [search, haste, shuffle] =>
    if search == "search your library and/or graveyard for an artifact creature card with mana value x or less and put it onto the battlefield with x additional +1/+1 counters on it" &&
        haste == "if x is 4 or greater, it gains haste until end of turn" &&
        shuffle == "if you search your library this way, shuffle" then
      let artifactCreature :=
        [
          .cardType .artifact,
          .cardType .creature,
          .manaValueAtMost .x]
      let found (zone : Selector) : CardAction :=
        .defineSelectorVariable n
          (.selected (.controller .this) (.range 1 1)
            (.intersection (zone :: artifactCreature)))
      let enter : List CardAction := [
        .putOntoBattlefield (.variable n),
        .putCounter (.variable n) .plusOnePlusOne .x,
        .if (.greaterOrEqual .x (.nat 4))
          [.continuous [.gainAbility (.variable n) (.keyword .haste)] .endOfTurn]]
      some ([
        .playerSelectAction (.controller .this) (.range 1 1) [
          .searchLibraryThenShuffle (.controller .this)
            (found (.union [.inLibrary, .inGraveyard]) :: enter),
          .sequence (found .inGraveyard :: enter)]],
        n + 1)
    else none
  | _ => none

/-- `Return target spell to its owner's hand. If the gift was promised, players can't cast spells this turn.`
The spell is target `n`. Promising the gift is an event since the start of
the game (CR 702.174k). Players can't cast spells until end of turn only
when that event has occurred. -/
def parseReturnSpellIfGiftCantCast (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [ret, lock] =>
    if sentenceIs ret "return target spell to its owner's hand" &&
        sentenceIs lock
          "if the gift was promised, players can't cast spells this turn" then
      some ([
        .returnToHand (.target n .spell),
        .if (.happened (.giftPromised .this) .gameStart) [
          .continuous [.forbid (.castSpell .all)] .endOfTurn]
      ], n + 1)
    else none
  | _ => none

/-- Every sentence of `text` must parse. An unrecognized sentence fails
the text. No sentences (reminder-only or empty text) succeeds with no actions.
Multi-sentence templates are tried before the sentence split. -/
def actionsFromText (cardName : String) (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  let oneAction (parsed : Option (CardAction × Nat)) : Option (List CardAction × Nat) :=
    parsed.map fun (action, n') => ([action], n')
  parseReturnSpellIfGiftCantCast text n <|>
    parseVisionQuest text n <|>
    parseExileAttackersSearchBasics text n <|>
    parseLookAtTopExileFaceDownPlayIf text n <|>
    parseCounterExilePermanentMayCast text n <|>
    parseCounterThenRecruitIfMv text n <|>
    parsePlusOneThenEachOtherIfFromGy text n <|>
    parseInsteadFromGraveyard text n <|>
    parsePlusOneThenFight text n <|>
    parseAddManaCombination text n <|>
    oneAction (parseDealDamageExileIfDies cardName text n) <|>
    oneAction (parsePumpExileIfDies text n) <|>
    oneAction (parsePutPlusOneThenGains text n) <|>
    List.foldlM (fun (acc, n) s =>
      (parseSentence cardName s n).map fun (a, n') => (acc ++ [a], n'))
      ([], n) (sentences text)

/-- Split off a Gatherer `//ADV//` Adventure section. A marker that shares
its line with the Adventure name keeps that name. -/
def splitAdventure (lines : List String) : List String × List String :=
  go lines []
where
  go : List String → List String → List String × List String
    | [], acc => (acc.reverse, [])
    | line :: rest, acc =>
      if line == "//ADV//" then (acc.reverse, rest)
      else
        match after? line "//ADV//" with
        | some restLine =>
          let adv := if restLine.isEmpty then rest else restLine :: rest
          (acc.reverse, adv)
        | none => go rest (line :: acc)

/-- `As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}.`
The sacrifice and the generic mana are alternatives announced at CR 601.2b.
The ability functions while this spell is on the stack (CR 113.6 / 604.2). -/
def parseAdditionalCostSacrificeOrPay (line : String) : Option CardPart :=
  match (after? (normLine line)
      "as an additional cost to cast this spell, sacrifice ").bind
      (split2? · " or pay ") with
  | some (obj, costText) =>
    match (dropArticle? obj).bind typesInPhrase, parseManaSymbols costText with
    | some ts, some [.generic k] =>
      some (.ability (.stackStatic (
        .additionalCost .this
          [.or [
            .sacrificeCount (permanentWith ts) 1,
            .mana [.generic k]]])))
    | _, _ => none
  | none => none

/-- Drop a leading ability word (`Ferocious —`) when that word is present.
Any other dash stays part of the text. -/
def withoutAbilityWord (s word : String) : String :=
  match split2? s "—" with
  | some (w, rest) => if w == word then rest else s
  | none => s

/-- Creatures this object's controller controls. -/
def creaturesYouControl : Selector :=
  permanentWith [.creature] [youControl]

/-- A creature you control with power 4 or greater. -/
def ferociousCreature : Selector :=
  permanentWith [.creature] [youControl, .powerAtLeast (Value.int 4)]

/-- Creatures you control are declared as attackers together (CR 508.3). -/
def youAttack : Trigger :=
  .attackSimultaneously creaturesYouControl .all []

/-- Effect of `Whenever you attack, <effect>`. -/
def youAttackEffect? (line : String) : Option String :=
  after? (normLine line) "whenever you attack, "

/-- `you control a creature with power 4 or greater`, the Ferocious condition. -/
def ferociousCondition : String :=
  "you control a creature with power 4 or greater, "

/-- `Ferocious —` has no rules meaning (CR 207.2c) and may be omitted. -/
def withoutFerocious (line : String) : String :=
  withoutAbilityWord (normLine line) "ferocious"

/-- `until end of turn, this creature gets +P/+0 and creatures you control gain trample.`
The bonus and trample both last until end of turn. A zero power, or any
toughness change, is a different ability. -/
def parseSourceGetsAndTeamTrample (effect : String) : Option CardAction :=
  (after? (norm effect) "until end of turn, ").bind fun rest =>
    (split2? rest " and creatures you control gain ").bind fun (pump, gained) =>
      (splitGetsOnly? pump).bind fun (who, ptText) =>
        if parsePumpWho who != some (.source .this) then none
        else
          match parsePowerToughness ptText, parseKeywordPhrase gained with
          | some (p, 0), some [.trample] =>
            if p == 0 then none
            else
              some (.continuous
                [.addPower (.source .this) (Value.int p),
                  .gainAbility creaturesYouControl (.keyword .trample)]
                .endOfTurn)
          | _, _ => none

/-- `Put a +1/+1 counter on each creature you control.`
One counter uses the singular noun. `each` is every creature you control. -/
def parsePutPlusOneOnEachYouControl (sentence : String) : Option CardAction :=
  match (after? (normSentence sentence) "put ").bind
      (split2? · " +1/+1 counter on each ") with
  | some (countText, who) =>
    match nounCount? countText false, parseControlledPhrase who with
    | some 1, some sel =>
      if sel == creaturesYouControl then
        some (.putCounter creaturesYouControl .plusOnePlusOne 1)
      else none
    | _, _ => none
  | none => none

/-- `Ferocious — Whenever this creature attacks while you control a creature
with power 4 or greater, <effect>.`
`Ferocious` is an ability word (CR 207.2c) and may be omitted. The “while”
clause is part of the trigger condition (CR 603.2): it is checked when this
creature attacks, and it is not checked again when the ability resolves.
The effect is gaining life, this creature getting +P/+T until end of turn,
this creature getting +P/+0 and your creatures gaining trample until end of
turn, or a +1/+1 counter on each creature you control. -/
def parseFerociousThisAttacks (line : String) : Option CardPart :=
  let s := withoutFerocious line
  let lead := "whenever this creature attacks while " ++ ferociousCondition
  (after? s lead).bind fun effect =>
    let gainLife :=
      match parseYouGainLife effect 0 with
      | some (.gainLife _ k, _) => some (.gainLife (.controller .this) k)
      | _ => none
    let pump :=
      (parsePumpUntilEndOfTurn effect).bind fun action =>
        (sourceGetsUntilEnd? action).map fun _ => action
    (gainLife <|> pump <|>
        parseSourceGetsAndTeamTrample effect <|>
        parsePutPlusOneOnEachYouControl effect).map fun action =>
      .ability (.triggeredWhile (.attack .this .all) (.any ferociousCreature) action)

/-- `Ferocious — Whenever you attack while you control a creature with power
4 or greater, you draw a card and lose 1 life.`
`Ferocious` may be omitted (CR 207.2c). “Whenever you attack” is one trigger
when creatures you control attack at the same time (CR 508.3 / 603.2d). -/
def parseFerociousYouAttack (line : String) : Option CardPart :=
  let s := withoutFerocious line
  let lead := "whenever you attack while " ++ ferociousCondition
  (after? s lead).bind parseYouDrawCardLoseLife |>.map fun action =>
    .ability (.triggeredWhile youAttack (.any ferociousCreature) action)

/-- `Ferocious — At the beginning of combat on your turn, if you control a
creature with power 4 or greater, put a +1/+1 counter on this creature.`
`Ferocious` may be omitted (CR 207.2c). Beginning of combat is CR 507.1.
The “if” is an intervening if (CR 603.4). -/
def parseFerociousBeginCombat (line : String) : Option CardPart :=
  let s := withoutFerocious line
  let lead := "at the beginning of combat on your turn, if " ++ ferociousCondition
  (after? s lead).bind parsePutPlusOneOnThis |>.map fun action =>
    .ability (.triggered (.combatStart (.controller .this))
      (.if (.any ferociousCreature) [action]))

/-- `you may have this creature's base power and toughness become P/T until end of turn.`
The change is optional. `this creature` is the source of this ability. -/
def parseMaySetBasePT (effect : String) : Option CardAction :=
  (after? (norm effect)
      "you may have this creature's base power and toughness become ").bind
    fun rest =>
      (before? rest " until end of turn").bind parsePowerToughness |>.map
        fun (p, t) =>
          .optional (.controller .this) (.continuous
            [.setBasePower (.source .this) (Value.int p),
              .setBaseToughness (.source .this) (Value.int t)]
            .endOfTurn)

/-- `Whenever a land you control enters,` after case-folding. -/
def landYouControlEnters : String :=
  "whenever a land you control enters, "

/-- Text after an optional `Landfall —` ability word (CR 207.2c). -/
def withoutLandfall (line : String) : String :=
  withoutAbilityWord (normLine line) "landfall"

/-- `Landfall — Whenever a land you control enters, <effect>.`
`Landfall` is an ability word (CR 207.2c) and may be omitted.
The effect is `this creature gets +P/+T until end of turn`,
`you may have this creature's base power and toughness become P/T until end of turn`,
or `put a +1/+1 counter on target <permanent> you control`.
`you control` is required on that target; a bare target is a different ability.
The target, when there is one, is `n`. A line that also says `choose one —`
is a modal trigger, not this ability. -/
def parseLandYouControlEnters (line : String) (n : Nat) : Option (CardPart × Nat) :=
  (after? (withoutLandfall line) landYouControlEnters).bind fun effect =>
    onTriggerN (.enter landsYouControl) <|
      match parsePumpUntilEndOfTurn effect with
      | some action => (sourceGetsUntilEnd? action).map fun _ => (action, n)
      | none =>
        match parseMaySetBasePT effect with
        | some action => some (action, n)
        | none =>
          if !effect.endsWith " you control" then none
          else parsePutPlusOneOnTarget effect n

/-- `When this Equipment enters, target opponent sacrifices a creature of their choice.`
The entering object is this card. The opponent is target `n` and chooses which
creature to sacrifice (CR 701.17a). -/
def parseEnterTargetOpponentSacrifices (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onEnterN cardName line fun effect =>
    (between? effect "target opponent sacrifices " " of their choice").bind fun obj =>
      (dropArticle? obj).bind fun named =>
        if named != "creature" then none
        else
          some (
            .sacrifice
              (.selected
                (.target n (.opponent (.controller .this)))
                (.range 1 1)
                (permanentWith [.creature] [.controlled (.targetReference n)])),
            n + 1)

/-- `ward {N}` with a positive generic cost. -/
def genericWard? (s : String) : Option Nat :=
  (after? (norm s) "ward ").bind positiveGeneric?

/-- `Equipped creature gets +2/+1.` Also `Enchanted creature gets +2/+2 and has flying.`
And `Equipped creature gets +2/+2 and has ward {1}.`
The bonus, keywords, or generic ward are static abilities of the Equipment
or Aura (CR 604.1 / 301.5 / 303.4). `and has` may be omitted. A zero bonus
is omitted. `+0/+0` is not an effect. A bonus that lasts until end of turn
is a different ability. Ward is a generic cost, not a keyword. -/
def parseEquippedGets (line : String) : Option (List CardPart) :=
  let rest? :=
    after? (normLine line) "equipped creature gets " <|>
      after? (normLine line) "enchanted creature gets "
  rest?.bind fun rest =>
    if (split2? rest " until end of turn").isSome then none
    else
      let parsed : Option (String × Option Nat × List Keyword) :=
        match split2? rest " and has " with
        | none => some (rest, none, [])
        | some (pt, has) =>
          match genericWard? has with
          | some n => some (pt, some n, [])
          | none =>
            match has.splitOn " and ward " with
            | [kwText, cost] =>
              match parseKeywordPhrase kwText, genericWard? ("ward " ++ cost) with
              | some kws, some n => some (pt, some n, kws)
              | _, _ => none
            | _ => (parseKeywordPhrase has).map fun kws => (pt, none, kws)
      parsed.bind fun (ptText, ward?, kws) =>
        match parsePowerToughness ptText with
        | some (p, t) =>
          if p == 0 && t == 0 then none
          else
            let keywordEffects :=
              kws.map fun k =>
                (.gainAbility (.hostOf .this) (.keyword k) : ContinuousEffect)
            let wardEffects :=
              match ward? with
              | none => []
              | some n =>
                [.gainAbility (.hostOf .this)
                  (.keywordWithCost .ward [.mana [.generic n]])]
            let effects :=
              flatPowerToughness (.hostOf .this) p t ++ keywordEffects ++ wardEffects
            if effects.isEmpty then none
            else some (effects.map fun e => .ability (.static e))
        | none => none

/-- `Equip {2}.` Reminder text such as
`({2}: Attach to target creature you control. Equip only as a sorcery.)`
is not rules text (CR 207.2 / 702.6). -/
def parseEquip (line : String) : Option CardPart :=
  match (after? (normLine line) "equip ").bind nonemptyMana? with
  | some syms => some (.ability (.keywordWithCost .equip [.mana syms]))
  | none => none

/-- `When <this> enters, create a colorless Equipment artifact token named Axe with "Equipped creature gets +1/+0" and equip {2}.`
The token is a colorless Equipment artifact with that name. Colorless is an
empty color indicator. The quoted text is a static ability of the token.
Equip is another ability of the token. A zero bonus is omitted. `+0/+0` is
not an effect. -/
def parseEnterCreateNamedEquipment (cardName : String) (line : String) :
    Option CardPart :=
  let raw := rulesText line
  let (raw, attach) :=
    match split2? raw ". Attach it to " with
    | some (rest, who) => if refersToSelf cardName who then (rest, true) else (raw, false)
    | none => (raw, false)
  (split2? raw " named ").bind fun (lead, rest) =>
    (split2? rest " with \"").bind fun (tokenName, afterName) =>
      (split2? afterName "\" and ").bind fun (quoted, equipText) =>
        if tokenName.isEmpty then none
        else
          onEnter cardName lead fun effect =>
            if effect != "create a colorless equipment artifact token" then none
            else
              match parseEquippedGets quoted, parseEquip equipText with
              | some quotedParts, some equipPart =>
                let create := CardAction.createTokens (.controller .this) 1
                  ([.name tokenName, .type .artifact, .subtype .equipment,
                    .colorIndicator []] ++
                    quotedParts ++ [equipPart])
                if attach then
                  some (.sequence [.actionId 1 create, .attach (.wasCreatedByAction 1) (.source .this)])
                else some create
              | _, _ => none

/-- `Each opponent loses 2 life.` The amount is a printed number. -/
def parseEachOpponentLosesLife (sentence : String) : Option Nat :=
  lifeAmount? (normSentence sentence) "each opponent loses "

/-- `When <this card> enters, exile up to one target card from an opponent's graveyard. Each opponent loses N life.`
Up to one target is zero or one (CR 115.1). That target is numbered `n`. -/
def parseEnterExileOppGyLoseLife (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences line with
  | [enter, lose] =>
    onEnterN cardName enter fun effect =>
      if effect != "exile up to one target card from an opponent's graveyard" then none
      else
        (parseEachOpponentLosesLife lose).map fun k =>
          (.sequence [
              .exile
                (.targets n (.range 0 1)
                  (.intersection [
                    .inGraveyard,
                    .owner (.opponent (.controller .this))])),
              .loseLife (.opponent (.controller .this)) (Value.nat k)],
           n + 1)
  | _ => none

def returnThisFromGraveyardToHand : CardAction :=
  .returnToHand (.intersection [.inGraveyard, .source .this])

def parseReturnThisFromGraveyard (sentence : String) : Option CardAction :=
  if sentenceIs sentence "return this card from your graveyard to your hand" then
    some returnThisFromGraveyardToHand
  else
    none

/-- `{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand. Activate only as a sorcery.`
The effect moves this card out of the graveyard, so the ability functions
there (CR 113.6). “Activate only as a sorcery” is the condition
(CR 307.1 / 117.1a). The ability is `graveyardActivatedIf`. -/
def parseGraveyardReturn (line : String) : Option CardPart :=
  (splitPrintedAbility? line).bind fun (costText, effect) =>
    match sentences effect with
    | [ret, restrict] =>
      if !sentenceIs restrict "activate only as a sorcery" then none
      else
        match parsePrintedCosts "" costText, parseReturnThisFromGraveyard ret with
        | some costs, some action =>
          some (.ability (
            .graveyardActivatedIf
              (.timeToCastSorcery (.controller .this))
              costs
              action))
        | _, _ => none
    | _ => none

/-- `When this creature enters, each opponent discards a card.`
The entering object is this card. -/
def parseEnterEachOpponentDiscards (cardName : String) (line : String) :
    Option CardPart :=
  onEnter cardName line fun effect =>
    (after? effect "each opponent discards ").bind parseCardCount |>.map fun k =>
      .discard (.opponent (.controller .this)) (Value.nat k)

/-- A pronoun for the object named earlier in the same ability. -/
def isPersonalPronoun (s : String) : Bool :=
  match norm s with
  | "he" | "she" | "it" | "they" => true
  | _ => false

/-- `When Gandalf enters, he deals 3 damage divided as you choose among one, two, or three targets.`
The entering object is this card. The damage source is a pronoun for that
object, or another reference to this card. Its controller divides the damage
(CR 601.2d). `targets` with no type is any target. The counts are a positive
contiguous range, and those targets are numbered `n`. -/
def parseEnterDividedDamage (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (before? (normLine line) " targets").bind fun body =>
    onEnterN cardName body fun effect =>
      (split2? effect " deals ").bind fun (who, rest) =>
        if who.isEmpty || !(isPersonalPronoun who || refersToSelf cardName who) then none
        else
          (split2? rest " damage divided as you choose among ").bind fun (amt, counts) =>
            match positiveCount amt, parseContiguousCounts counts with
            | some amount, some (lo, hi) =>
              some (
                .divideDamage
                  (.controller .this)
                  (.source .this)
                  (.targets n (.range (Value.nat lo) (Value.nat hi)) .all)
                  (Value.nat amount),
                n + 1)
            | _, _ => none

/-- `When this Equipment enters, you may discard a card. If you do, draw two cards.`
The entering object is this card. “If you do” means the draw happens only
when that discard is taken. The discard is action `n`. -/
def parseEnterMayDiscardDraw (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences line with
  | [may, ifYouDo] =>
    onEnterN cardName may fun effect =>
      (after? effect "you may discard ").bind fun discardedText =>
        match parseCardCount discardedText,
            (after? (norm ifYouDo) "if you do, draw ").bind parseCardCount with
        | some discarded, some drawn =>
          some (
            .sequence [
              .optional (.controller .this)
                (.actionId n
                  (.discard (.controller .this) (Value.nat discarded))),
              .if
                (.happened (.actionWithId n) .gameStart)
                [.draw (.controller .this) (Value.nat drawn)]],
            n + 1)
        | _, _ => none
  | _ => none

/-- `Galion's` or `this creature's` names this card. -/
def possessiveSelf (cardName whose : String) : Bool :=
  (before? (norm whose) "'s").any (refersToSelf cardName)

/-- `up to one other target creature you control` as zero or one other
permanent of those types you control (CR 115.1). -/
def parseUpToOneOtherYouControl (s : String) : Option Selector :=
  (between? (norm s) "up to one other target " " you control").bind fun obj =>
    parseControlledPhrase ("other " ++ obj ++ " you control")

/-- `Whenever Galion attacks, choose up to one other target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn.`
The attacker is this card. The chosen creature is target `n`. -/
def parseAttackSetBasePT (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences line with
  | [attack, become] =>
    onAttackN cardName attack fun effect =>
      (after? effect "choose ").bind parseUpToOneOtherYouControl |>.bind fun among =>
        (between? (normSentence become)
            "its base power and toughness become equal to "
            " power and toughness until end of turn").bind fun whose =>
          if !possessiveSelf cardName whose then none
          else
            some (
              .continuous
                [.setBasePower
                  (.targets n (.range 0 1) among)
                  (Value.greatestPower (.source .this)),
                 .setBaseToughness
                  (.targetReference n)
                  (Value.greatestToughness (.source .this))]
                .endOfTurn,
              n + 1)
  | _ => none

/-- `Whenever another Elf you control enters, this creature gets +1/+1 until end of turn.`
`another` excludes this object. -/
def parseAnotherElfEntersGets (line : String) : Option CardPart :=
  triggeredSourcePump (normLine line) "whenever another elf you control enters, "
    (.enter
      (.intersection [
        .not .this,
        .permanent,
        .subtype .elf,
        youControl]))
    (· == (1, 1))

/-- `{T}: Add X mana of any one color, where X is this creature's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources.`
The tap symbol is the cost. X is this creature's power. The produced mana is
action `n`. -/
def parseTapAddAnyColorEqualToPower (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (splitPrintedAbility? line).bind
    fun (costText, effect) =>
      if norm costText != "{t}" then none
      else
        match sentences effect with
        | [add, spend] =>
          (after? (normSentence add) "add x mana of any one color, where x is ").bind
              (before? · " power") |>.bind fun whose =>
            if possessiveSelf cardName whose &&
                sentenceIs spend
                  "spend this mana only to cast elf spells and activate abilities of elf sources" then
              some (
                .ability (
                  .activated
                    [.tapSymbol]
                    (.sequence [
                      .actionId n
                        (.addManaOfOneColor
                          (.controller .this)
                          ManaSymbol.anyColor
                          (.greatestPower .this)),
                      .continuous
                        [.forbid
                          (.spendManaCreatedByAction n
                            (.not
                              (.or
                                (.castSpell (.subtype .elf))
                                (.activateAbility (.subtype .elf)))))]
                        .endOfTurn])),
                n + 1)
            else none
        | _ => none

/-- `<this>'s power and toughness are each equal to the number of lands you control.`
A characteristic-defining ability (CR 208.2a / 604.3). -/
def parseLandsCharacteristic (cardName : String) (line : String) : Option (List CardPart) :=
  (before? (normLine line) (" " ++ landsCharacteristicSuffix)).bind fun whose =>
    if possessiveSelf cardName whose then
      some (powerToughnessEqualLandsAbilities.map fun a => .ability a)
    else none

/-- The printed clause after `<this>'s`. -/
def creaturesPowerSuffix : String :=
  "power is equal to the number of creatures you control"

/-- `<this>'s power is equal to the number of creatures you control.`
A characteristic-defining ability (CR 208.2a / 604.3). Power is set to that
count. Toughness is not changed. -/
def parseCreaturesPowerCharacteristic (cardName : String) (line : String) :
    Option (List CardPart) :=
  (before? (normLine line) (" " ++ creaturesPowerSuffix)).bind fun whose =>
    if possessiveSelf cardName whose then
      some [.ability (.static (.setPower .this (.count creaturesYouControl)))]
    else none

/-- `<this>'s power is equal to the number of cards in your hand.`
A characteristic-defining ability (CR 208.2a / 604.3). Toughness is not
changed. -/
def parseCardsInHandPowerCharacteristic (cardName : String) (line : String) :
    Option (List CardPart) :=
  (before? (normLine line) " power is equal to the number of cards in your hand").bind
    fun whose =>
      if possessiveSelf cardName whose then
        some [.ability (.static (.setPower .this
          (.count (.intersection [.inHand, .owner (.controller .this)]))))]
      else none

/-- `When this creature enters, search your library for a Forest card, put that card onto the battlefield, then shuffle.`
The entering object is this card. -/
def parseEnterSearchForest (cardName : String) (line : String) : Option CardPart :=
  onEnter cardName line fun effect =>
    if sentenceIs effect
        "search your library for a forest card, put that card onto the battlefield, then shuffle" then
      some (.searchLibraryThenShuffle
        (.controller .this)
        [.putOntoBattlefield
          (.selected
            (.controller .this)
            (.range 1 1)
            (.intersection [.inLibrary, .subtype .forest]))])
    else none

/-- One card part that does not advance the target number. -/
def sole (part? : Option CardPart) (n : Nat) : Option (List CardPart × Nat) :=
  part?.map fun part => ([part], n)

/-- One card part together with the target number it produced. -/
def carry (parsed : Option (CardPart × Nat)) : Option (List CardPart × Nat) :=
  parsed.map fun (part, n') => ([part], n')

/-- Spell actions. Empty actions are a failed parse, not a blank spell. -/
def spellActions (parsed : Option (List CardAction × Nat)) : Option (List CardPart × Nat) :=
  parsed.bind fun (actions, n') =>
    if actions.isEmpty then none else some ([.actions actions], n')

/-- `<this> enters tapped.` A replacement effect (CR 614.1). A spell does not
enter the battlefield. -/
def parseEntersTapped (cardName line : String) : Option CardPart :=
  (before? (normLine line) " enters tapped").bind fun subject =>
    if subject.isEmpty || norm subject == "this spell" ||
        !refersToSelf cardName subject then
      none
    else
      some (.ability (.static (.replace (.enter .this)
        [.putOntoBattlefieldInState .this [.tapped]])))

/-- `<this> enters tapped unless you control an Equipment.`
It enters tapped while its controller controls no Equipment. The ability
functions in every zone (CR 113.6) so it can replace how this card enters
the battlefield. -/
def parseEntersTappedUnlessEquipment (cardName line : String) : Option CardPart :=
  (split2? (normLine line) " enters tapped unless you control ").bind
    fun (subject, rest) =>
      if !refersToSelf cardName subject then none
      else
        match dropArticle? rest with
        | some "equipment" =>
          some (.ability (.everywhereStatic (.if (.not (.any equipmentYouControl))
            [.replace (.enter .this)
              [.putOntoBattlefieldInState .this [.tapped]]])))
        | _ => none

/-- One colored or colorless symbol that can be added to a mana pool. -/
def addableSymbol? (s : String) : Option ManaSymbol :=
  match parseManaSymbols s with
  | some [sym] =>
    match CardAction.addedManaType? sym with
    | some _ => some sym
    | none => none
  | _ => none

/-- `Add {G} or {U}`: the player chooses one listed symbol. -/
def parseAddOneOf (effect : String) : Option (List CardAction) :=
  (after? (normSentence effect) "add ").bind fun rest =>
    let options := rest.splitOn " or " |>.map copied |>.filter (· != "")
    if options.length < 2 then none
    else
      options.mapM fun opt =>
        (addableSymbol? opt).map fun sym => .addMana (.controller .this) [sym]

/-- `{T}: Add {G} or {U}.` The tap symbol is the cost (CR 107.5). -/
def parseTapAddOneOf (line : String) : Option CardPart :=
  (splitPrintedAbility? line).bind
    fun (costText, effect) =>
      if norm costText != "{t}" then none
      else
        (parseAddOneOf effect).map fun actions =>
          .ability (.activated [.tapSymbol]
            (.playerSelectAction (.controller .this) (.range 1 1) actions))

/-- One word of a typecycling type phrase. -/
def addCyclingWord
    (acc : Option (List CardSupertype × List CardType × List CardSubtype))
    (w : String) : Option (List CardSupertype × List CardType × List CardSubtype) :=
  acc.bind fun (sups, tys, sts) =>
    match supertypeOfOracle? w with
    | some s => some (sups ++ [s], tys, sts)
    | none =>
      match typeOfOracle? w with
      | some t => some (sups, tys ++ [t], sts)
      | none =>
        match subtypeOfOracle? w with
        | some st => some (sups, tys, sts ++ [st])
        | none => none

/-- `Halfling` or `Basic land` as the type a cycling ability searches for. -/
def parseCyclingWords (phrase : String) :
    Option (List CardSupertype × List CardType × List CardSubtype) :=
  let words := (norm phrase).splitOn " " |>.map copied |>.filter (· != "")
  if words.isEmpty then none
  else
    match words.foldl addCyclingWord (some ([], [], [])) with
    | some (sups, tys, sts) =>
      if tys.isEmpty && sts.isEmpty then none else some (sups, tys, sts)
    | none => none

/-- `Halflingcycling {4}`. Reminder text is not rules text (CR 702.29). -/
def parseTypecycling (line : String) : Option CardPart :=
  let line := rulesText line
  let (phrase, costText) := splitNameCost line
  if costText.isEmpty then none
  else
    (before? (norm phrase) "cycling").bind fun kind =>
      match parseCyclingWords kind, nonemptyMana? costText with
      | some (sups, tys, sts), some syms =>
        some (.ability (.keywordWithCost (.typecycling sups tys sts) [.mana syms]))
      | _, _ => none

/-- `When this Equipment enters, you gain 2 life.` The entering object is this card. -/
def parseEnterYouGainLife (cardName line : String) : Option CardPart :=
  onEnter cardName line fun effect => actionOf (parseYouGainLife effect 0)

/-- Search for one basic land, reveal it, hold it out of the shuffle, then
put that card on top. The found card is variable `n`. -/
def searchBasicLandOnTop (n : Nat) : CardAction :=
  .sequence [
    .searchLibraryThenShuffle (.controller .this) [
      .defineSelectorVariable n
        (.selected (.controller .this) (.range 1 1) basicLandInLibrary),
      .reveal (.variable n),
      .holdOutInLibrary (.variable n)],
    .putOnTopOfLibrary (.variable n)]

/-- `You may search your library for a basic land card, reveal it, then shuffle and put that card on top.`
The found card is variable `n`. -/
def parseMaySearchBasicOnTop (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence
      "you may search your library for a basic land card, reveal it, then shuffle and put that card on top" then
    some (.optional (.controller .this) (searchBasicLandOnTop n), n + 1)
  else none

/-- `When <this> enters, you gain N life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top.`
The entering object is this card. The found card is variable `n`. -/
def parseEnterGainLifeMaySearchBasicOnTop (cardName line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences line with
  | [enter, search] =>
    onEnterN cardName enter fun effect =>
      match actionOf (parseYouGainLife effect n), parseMaySearchBasicOnTop search n with
      | some gain, some (maySearch, n') =>
        some (.sequence [gain, maySearch], n')
      | _, _ => none
  | _ => none

/-- `When this creature enters, untap another target creature you control. If that creature is a Bear, put a +1/+1 counter on it.`
The creature is target `n`. `another` excludes this object. -/
def parseEnterUntapPlusOneIfSubtype (cardName line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences line with
  | [enter, ifSubtype] =>
    onEnterN cardName enter fun effect =>
      (after? effect "untap ").bind parseBattlefieldTarget |>.bind fun sel =>
        if !sel.shape.anotherCreatureYouControl then none
        else
          (between? (normSentence ifSubtype)
              "if that creature is " ", put a +1/+1 counter on it").bind
            dropArticle? |>.bind subtypeOfOracle? |>.map fun st =>
            (.sequence [
                .untap (.target n sel),
                .if
                  (.anySubtype (.targetReference n) st)
                  [.putCounter (.targetReference n) .plusOnePlusOne 1]],
             n + 1)
  | _ => none

/-- `recruit` as a keyword action of this card's controller. -/
def recruitEffect? (effect : String) : Option CardAction :=
  if effect == "recruit" then some (.keyword (.controller .this) .recruit) else none

/-- `When <this card> enters, recruit.`
Recruit is a keyword action of this card's controller. A reminder
parenthetical is not rules text (CR 207.2). -/
def parseEnterRecruit (cardName : String) (line : String) : Option CardPart :=
  onEnter cardName line recruitEffect?

/-- `When <this card> dies, recruit.`
Recruit is a keyword action of this card's controller. A reminder
parenthetical is not rules text (CR 207.2). -/
def parseDiesRecruit (cardName : String) (line : String) : Option CardPart :=
  onDies cardName line recruitEffect?

/-- `When <this card> enters, scry N.`
`N` is a positive printed number. A reminder parenthetical is not rules text. -/
def parseEnterScry (cardName : String) (line : String) : Option CardPart :=
  onEnter cardName line fun effect => actionOf (parseScry effect 0)

/-- `create a Treasure token` or `create a tapped Treasure token`.
A tapped token enters tapped (CR 110.5). -/
def parseCreateTreasure (sentence : String) : Option CardAction :=
  match normSentence sentence with
  | "create a tapped treasure token" =>
    some (.createTokens (.controller .this) 1 PredefinedToken.treasureToken [.tapped])
  | "create a treasure token" =>
    some (.createTokens (.controller .this) 1 PredefinedToken.treasureToken)
  | _ => none

/-- `When <this card> enters, create a Treasure token.`
Also `create a tapped Treasure token`. -/
def parseEnterCreateTreasure (cardName : String) (line : String) : Option CardPart :=
  onEnter cardName line parseCreateTreasure

/-- `When <this card> enters, exile the top card of your library. Until the end of your next turn, you may play that card.`
The exile is action `n`. The exiled card may be played until the end of your
next turn (CR 611.2a). -/
def parseEnterExileTopMayPlay (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences line with
  | [enter, play] =>
    onEnterN cardName enter fun effect =>
      if !sentenceIs effect "exile the top card of your library" then none
      else if !sentenceIs play
          "until the end of your next turn, you may play that card" then none
      else some (exileTopPlayUntilEndOfNextTurn n, n + 1)
  | _ => none

/-- `This spell can't be countered.`
Countering this spell is forbidden. The ability functions while this spell
is on the stack (CR 113.6b). -/
def parseCantBeCountered (line : String) : Option CardPart :=
  if sentenceIs (rulesText line) "this spell can't be countered" then
    some (.ability (.stackStatic (.forbid (.counter .this))))
  else none

/-- A noncreature spell this object's controller casts. -/
def noncreatureSpellYouCast : Selector :=
  .intersection [.spell, .not (.cardType .creature), youControl]

/-- Effect of `Whenever you cast a noncreature spell, <effect>`. -/
def youCastNoncreatureEffect? (line : String) : Option String :=
  after? (normLine line) "whenever you cast a noncreature spell, "

/-- `Whenever you cast a noncreature spell, amass Goblins 1.`
Amass is a keyword action of this card's controller. A reminder
parenthetical is not rules text (CR 207.2). -/
def parseYouCastNoncreatureAmass (line : String) : Option CardPart :=
  onTrigger (.castSpell noncreatureSpellYouCast)
    ((youCastNoncreatureEffect? line).bind parseAmass)

/-- `Whenever you cast a noncreature spell, <this> gets +1/+1 until end of turn and deals 1 damage to each opponent.`
`<this>` is this card. The bonus lasts until end of turn. `N` is a positive
count. Each opponent of this object's controller is dealt that damage. -/
def parseYouCastNoncreaturePumpAndDamage (cardName : String) (line : String) :
    Option CardPart :=
  (youCastNoncreatureEffect? line).bind fun effect =>
    (split2? effect " until end of turn and deals ").bind fun (pump, damage) =>
      (splitGetsOnly? pump).bind fun (who, ptText) =>
        (before? damage " damage to each opponent").bind fun amt =>
          if !refersToSelf cardName who then none
          else
            match parsePowerToughness ptText, positiveCount amt with
            | some (p, t), some n =>
              (pumpUntilEnd (.source .this) p t none).map fun pumpAction =>
                .ability (.triggered
                  (.castSpell noncreatureSpellYouCast)
                  (.sequence [
                    pumpAction,
                    .dealDamage (.source .this)
                      (.opponent (.controller .this)) (.nat n)]))
            | _, _ => none

/-- `When <this card> enters, amass Goblins 1.`
The entering object is this card. -/
def parseEnterAmass (cardName : String) (line : String) : Option CardPart :=
  onEnter cardName line parseAmass

/-- `When <this card> dies, amass Goblins 4.`
The dying object is this card. -/
def parseDiesAmass (cardName : String) (line : String) : Option CardPart :=
  onDies cardName line parseAmass

/-- `Whenever you attack, amass Goblins 2.`
“Whenever you attack” is one trigger when creatures you control attack at
the same time (CR 508.3 / 603.2d). -/
def parseYouAttackAmass (line : String) : Option CardPart :=
  onTrigger youAttack ((youAttackEffect? line).bind parseAmass)

/-- `Whenever you attack, recruit.`
“Whenever you attack” is one trigger when creatures you control attack at
the same time (CR 508.3 / 603.2d). A reminder parenthetical is not rules text. -/
def parseYouAttackRecruit (line : String) : Option CardPart :=
  onTrigger youAttack ((youAttackEffect? line).bind recruitEffect?)

/-- `You may cast this spell as though it had flash if you control a Human.`
The permission is checked as you begin to cast this spell, before the card
is put onto the stack (CR 601.3 / 702.8). `you` is `Selector.caster`, the
player who would cast the spell. The spell does not gain flash. -/
def parseCastAsThoughFlash (line : String) : Option CardPart :=
  (after? (normLine line)
      "you may cast this spell as though it had flash if you control ").bind
    dropArticle? |>.bind subtypeOfOracle? |>.map fun st =>
      .ability (.everywhereStatic (
        .canBeCastAsThoughWithFlashIf
          .this
          (.any (.intersection [.permanent, .subtype st, .controlled .caster]))))

/-- `<permanents> get +P/+T.` No duration is printed, so this is a static
ability (CR 604.2 / 613.4c). A zero bonus is omitted. `+0/+0` is not an
effect. A bonus that lasts until end of turn is a different ability. -/
def parseStaticGets (line : String) : Option (List CardPart) :=
  let s := normLine line
  if (split2? s " until end of turn").isSome then none
  else
    (splitGets? s).bind fun (who, ptText) =>
      match parseControlledPhrase who, parsePowerToughness ptText with
      | some sel, some (p, t) => staticPowerToughness sel p t
      | _, _ => none

/-- `Whenever <this card> enters or attacks, recruit.`
Recruit is a keyword action of this card's controller. A reminder
parenthetical is not rules text (CR 207.2). -/
def parseEnterOrAttackRecruit (cardName : String) (line : String) : Option CardPart :=
  (triggerSelfEffect? cardName "whenever" (normLine line) " enters or attacks, ").bind
    recruitEffect? |>.map fun action =>
      .ability (.triggered (.or (.enter .this) (.attack .this .all)) action)

/-- `When <this card> enters, put a +1/+1 counter on target <permanent>.`
The entering object is this card. The target is `n`. -/
def parseEnterPutPlusOneOnTarget (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onEnterN cardName line (parsePutPlusOneOnTarget · n)

/-- A color word such as `red` or `green`. -/
def colorName? (s : String) : Option Color :=
  match norm s with
  | "white" => some .white
  | "blue" => some .blue
  | "black" => some .black
  | "red" => some .red
  | "green" => some .green
  | _ => none

/-- Unsigned `2/2`. A sign is a pump, not a token's power and toughness. -/
def parseUnsignedPT (s : String) : Option (Nat × Nat) :=
  (split2? s "/").bind fun (p, t) =>
    match natOfDigits? p, natOfDigits? t with
    | some p, some t => some (p, t)
    | _, _ => none

/-- The subtype whose printed plural is `word` (`Wolves` is Wolf). -/
def pluralCreatureType? (word : String) : Option CardSubtype :=
  cardSubtypes.find? fun st =>
    norm (StaticAbility.pluralSubtype (toString st)) == norm word

/-- `Other Elves you control get +1/+1.`
No duration is printed, so this is a static ability. The subtype is plural.
A zero bonus is omitted. `+0/+0` is not an effect. -/
def parseOtherSubtypeYouControlGets (line : String) : Option (List CardPart) :=
  let s := normLine line
  if (split2? s " until end of turn").isSome then none
  else
    (after? s "other ").bind fun rest =>
      (split2? rest " you control get ").bind fun (plural, ptText) =>
        match pluralCreatureType? plural, parsePowerToughness ptText with
        | some st, some (p, t) =>
          staticPowerToughness
            (.intersection [
              .not .this, .permanent, .cardType .creature, .subtype st, youControl])
            p t
        | _, _ => none

/-- `create a 2/2 red Dwarf creature token` or
`create two 2/2 green Wolf creature tokens`.
One token uses the singular noun. More than one uses the plural.
The token is a creature of that power, toughness, color, and subtype. -/
def parseCreateColoredCreatureToken (sentence : String) : Option CardAction :=
  (after? (normSentence sentence) "create ").bind fun rest =>
    match rest.splitOn " " |>.map copied |>.filter (· != "") with
    | [countText, pt, colorText, subtypeText, creatureWord, tokenWord] =>
      let plural := tokenWord == "tokens"
      if creatureWord != "creature" || (tokenWord != "token" && !plural) then none
      else
        match nounCount? countText plural, parseUnsignedPT pt,
            colorName? colorText, subtypeOfOracle? subtypeText with
        | some n, some (p, t), some c, some st =>
          some (.createTokens (.controller .this) (Value.nat n) [
            .type .creature,
            .subtype st,
            .colorIndicator [c],
            .power p,
            .toughness t])
        | _, _, _, _ => none
    | _ => none

/-- `Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.`
`Landfall` is an ability word (CR 207.2c) and may be omitted. -/
def parseLandfallCreate (line : String) : Option CardPart :=
  (after? (withoutLandfall line) landYouControlEnters).bind
    parseCreateColoredCreatureToken |>.map fun action =>
      .ability (.triggered (.enter landsYouControl) action)

/-- `This ability costs {1} less to activate for each Equipment you control.`
`{N}` is generic mana. Zero is not a reduction. -/
def parseAbilityCostsLessPerEquipment (sentence : String) : Option Nat :=
  (between? (normSentence sentence)
      "this ability costs " " less to activate for each equipment you control").bind
    positiveGeneric?

/-- `{4}{R}, {T}: Create a 2/2 red Dwarf creature token. This ability costs {1} less to activate for each Equipment you control. Activate only as a sorcery.`
The reduction is `{N}` for each Equipment this object's controller controls.
It is a static effect of that activated ability. `.this` in the effect is
the ability. Sorcery timing is the activation restriction. -/
def parseActivatedCreateCostsLess (cardName line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  (splitPrintedAbility? line).bind
    fun (costText, effect) =>
      let (body, limit) := splitActivateLimit (sentences effect)
      match body, limit with
      | [createText, lessText], .asSorcery =>
        match parseCreateColoredCreatureToken createText,
            parseAbilityCostsLessPerEquipment lessText,
            parsePrintedCosts cardName costText with
        | some create, some k, some costs =>
          some ([
            .ability (.activatedWithStaticIf
              (.timeToCastSorcery (.controller .this))
              costs
              create
              (.reduceCostWithX .this
                [.mana [.generic k]]
                (.count equipmentYouControl)))],
            n)
        | _, _, _ => none
      | _, _ => none

/-- `<this> to it`: attach this object to the token just created. -/
def attachSelfToIt? (cardName s : String) : Bool :=
  (before? (norm s) " to it").any (refersToSelf cardName)

/-- `<this> to the amassed Army`: attach this object to the Army just amassed. -/
def attachSelfToAmassedArmy? (cardName s : String) : Bool :=
  (before? (norm s) " to the amassed army").any (refersToSelf cardName)

/-- `Whenever an artifact you control enters, draw a card.`
One card. Drawing more than one is a different ability. -/
def parseArtifactYouControlEntersDraw (line : String) : Option CardPart :=
  (after? (normLine line) "whenever an artifact you control enters, ").bind
      fun effect =>
    match (after? effect "draw ").bind parseCardCount with
    | some 1 =>
      some (.ability (.triggered
        (.enter (permanentWith [.artifact] [youControl]))
        (.draw (.controller .this) 1)))
    | _ => none

/-- `<this> can't attack unless you control two or more other Wolves.`
The subject is this card. The subtype is plural. Attacking is forbidden
while its controller controls fewer than that many other permanents of
that subtype. -/
def parseCantAttackUnlessNOther (cardName : String) (line : String) : Option CardPart :=
  (split2? (normLine line) " can't attack unless you control ").bind fun (subject, rest) =>
    if !refersToSelf cardName subject then none
    else
      (split2? rest " or more other ").bind fun (countText, plural) =>
        match positiveCount countText, pluralCreatureType? plural with
        | some n, some st =>
          some (.ability (.static (.if
            (.less
              (.count
                (.intersection [
                  .not .this,
                  .permanent,
                  .subtype st,
                  youControl]))
              (Value.nat n))
            [.forbid (.attack .this .all)])))
        | _, _ => none

/-- `At the beginning of your upkeep, create a 2/2 green Wolf creature token.`
Also `create a Treasure token`. `your` is this object's controller. -/
def parseUpkeepCreateCreature (line : String) : Option CardPart :=
  (after? (normLine line) "at the beginning of your upkeep, ").bind fun effect =>
    (parseCreateColoredCreatureToken effect <|> parseCreateTreasure effect).map
      fun action =>
        .ability (.triggered (.upkeep (.controller .this)) action)

/-- `When this Equipment enters, create a 2/2 red Dwarf creature token, then attach this Equipment to it.`
One token is created. This object is attached to that token. The creation
is action `n`. -/
def parseEnterCreateThenAttach (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onEnterN cardName line fun effect =>
    (split2? effect ", then attach ").bind fun (createText, attachText) =>
      match parseCreateColoredCreatureToken createText with
      | some (.createTokens who (.nat 1) parts []) =>
        if who == .controller .this && attachSelfToIt? cardName attachText then
          some (
            .sequence [
              .actionId n (.createTokens who 1 parts),
              .attach .this (.wasCreatedByAction n)],
            n + 1)
        else none
      | _ => none

/-- `When this Equipment enters, amass Goblins 1, then attach this Equipment to the amassed Army.`
Amass is a keyword action of this card's controller. This object is attached
to the Army that action amassed. The amass is action `n`. A reminder
parenthetical is not rules text. -/
def parseEnterAmassThenAttach (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onEnterN cardName line fun effect =>
    (split2? effect ", then attach ").bind fun (amassText, attachText) =>
      match parseAmass amassText with
      | some amass =>
        if attachSelfToAmassedArmy? cardName attachText then
          some (
            .sequence [
              .actionId n amass,
              .attach .this (.wasObjectOfAction n)],
            n + 1)
        else none
      | none => none

/-- `Enchant creature.` Enchant (CR 702.5). The permanent is target `n`. -/
def parseEnchant (line : String) (n : Nat) : Option (CardPart × Nat) :=
  (after? (normLine line) "enchant ").bind fun rest =>
    (parseBattlefieldTarget ("target " ++ rest)).map fun sel =>
      (.ability (.keywordWithTarget .enchant n sel), n + 1)

/-- `Ward {3}`. A positive generic cost (CR 702.21). A reminder parenthetical
is not rules text. -/
def parseWard (line : String) : Option CardPart :=
  (genericWard? (normLine line)).map fun n =>
    .ability (.keywordWithCost .ward [.mana [.generic n]])

/-- `Each creature you control with a +1/+1 counter on it has menace.`
A reminder parenthetical is not rules text. -/
def parseCreaturesWithPlusOneHaveMenace (line : String) : Option CardPart :=
  if sentenceIs (normLine line)
      "each creature you control with a +1/+1 counter on it has menace" then
    some (.ability (.static (.gainAbility
      (.intersection [
        .permanent, .cardType .creature, youControl, .hasCounter .plusOnePlusOne])
      (.keyword .menace))))
  else none

/-- `Creatures you control with +1/+1 counters on them have trample.` -/
def parseCreaturesWithPlusOneHave (line : String) : Option (List CardPart) :=
  (after? (normLine line) "creatures you control with +1/+1 counters on them have ").bind
    parseKeywordPhrase |>.map fun kws =>
      kws.map fun k => .ability (.static (.gainAbility
        (.intersection [
          .permanent, .cardType .creature, youControl, .hasCounter .plusOnePlusOne])
        (.keyword k)))

/-- `At the beginning of your end step, draw a card.`
`your` is this object's controller. One card. -/
def parseYourEndStepDraw (line : String) : Option CardPart :=
  (after? (normLine line) "at the beginning of your end step, ").bind fun effect =>
    match (after? effect "draw ").bind parseCardCount with
    | some 1 =>
      some (.ability (.triggered
        (.endStep (.controller .this))
        (.draw (.controller .this) 1)))
    | _ => none

/-- `attach it to target Dwarf you control`. `it` or this card is the
attachment. The destination is target `n`. -/
def parseAttachSelfToTarget (cardName effect : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence effect) " to ").bind fun (head, dest) =>
    (after? head "attach ").bind fun subject =>
      if subject != "it" && !refersToSelf cardName subject then none
      else
        (parseBattlefieldTarget dest).map fun sel =>
          (.attach .this (.target n sel), n + 1)

/-- `When this Equipment enters, attach it to target Dwarf you control.`
The entering object is this card. -/
def parseEnterAttachToTarget (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onEnterN cardName line (parseAttachSelfToTarget cardName · n)

/-- `attach target Equipment you control to up to one target creature you control.`
The Equipment is target `n`. Up to one creature is target `n + 1`. -/
def parseAttachTargetEquipment (effect : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (after? (normSentence effect) "attach target equipment you control to ").bind
    fun dest =>
      let upToOne :=
        if dest == "up to one target creature you control" then
          some (.targets (n + 1) (.range 0 1) creaturesYouControl)
        else if dest == "target creature you control" then
          some (.target (n + 1) creaturesYouControl)
        else none
      upToOne.map fun creature =>
        (.attach (.target n equipmentYouControl) creature, n + 2)

/-- `When <this> enters, attach target Equipment you control to up to one target creature you control.`
The entering object is this card. -/
def parseEnterAttachTargetEquipment (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onEnterN cardName line (parseAttachTargetEquipment · n)

/-- A spell or ability controlled by an opponent of this object's controller. -/
def spellOrAbilityOpponentControls : Selector :=
  .intersection [
    .union [.spell, .ability],
    .controlled (.opponent (.controller .this))]

/-- `Whenever <this> becomes the target of a spell or ability an opponent controls, draw a card.`
One card. The spell or ability is the first argument of `target`; this
object is the target. One trigger, even if that spell or ability targets
this more than once. -/
def parseBecomesTargetDraw (cardName : String) (line : String) : Option CardPart :=
  (triggerSelfEffect? cardName "whenever" (normLine line)
      " becomes the target of a spell or ability an opponent controls, ").bind
    fun effect =>
      match (after? effect "draw ").bind parseCardCount with
      | some 1 =>
        some (.ability (.triggered
          (.target spellOrAbilityOpponentControls .this)
          (.draw (.controller .this) 1)))
      | _ => none

/-- `At the beginning of your first main phase, add {R}{R}.`
`your` is this object's controller. Every symbol must be mana that can be added. -/
def parseFirstMainAddMana (line : String) : Option CardPart :=
  (after? (normLine line) "at the beginning of your first main phase, add ").bind
    nonemptyMana? |>.bind fun syms =>
      match CardAction.addedManaTypes? syms with
      | some _ =>
        some (.ability (.triggered
          (.precombatMainPhase (.controller .this))
          (.addMana (.controller .this) syms)))
      | none => none

/-- `Crew 2`. Crew (CR 702.122). `N` is the number of creatures to tap.
A reminder parenthetical is not rules text. -/
def parseCrew (line : String) : Option CardPart :=
  (after? (normLine line) "crew ").bind positiveCount |>.map fun n =>
    .ability (.keyword (.crew n))

/-- `Teamwork 2`. Teamwork (CR 702.194). `N` is a positive total power.
A reminder parenthetical is not rules text. -/
def parseTeamwork (line : String) : Option CardPart :=
  (after? (normLine line) "teamwork ").bind positiveCount |>.map fun n =>
    .ability (.keyword (.teamwork n))

/-- `Gift a Food`, `Gift a card`, `Gift a tapped Fish`, `Gift an extra turn`,
`Gift a Treasure`, or `Gift an Octopus` (CR 702.174d–i). A reminder
parenthetical is not rules text. -/
def parseGift (line : String) : Option CardPart :=
  let gift? :=
    match normLine line with
    | "gift a food" => some Gift.food
    | "gift a card" => some Gift.card
    | "gift a tapped fish" => some Gift.tappedFish
    | "gift an extra turn" => some Gift.extraTurn
    | "gift a treasure" => some Gift.treasure
    | "gift an octopus" => some Gift.octopus
    | _ => none
  gift?.map fun g => .ability (.keyword (.gift g))

/-- `him`, `her`, `them`, or `it`: the object named earlier in this ability. -/
def isObjectPronoun (s : String) : Bool :=
  match norm s with
  | "him" | "her" | "them" | "it" => true
  | _ => false

/-- `{6}: Gandalf's owner shuffles him into their library and draws three cards.`
The owner is bound to variable `n` before the shuffle. That recorded
player draws afterward. -/
def parseOwnerShuffleDraw (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (splitPrintedAbility? line).bind
    fun (costText, effect) =>
      (parseActivationCost cardName costText).bind fun costs =>
        (split2? (normSentence effect) " owner shuffles ").bind fun (whose, rest) =>
          if !possessiveSelf cardName whose then none
          else
            (split2? rest " into their library and draws ").bind fun (obj, countText) =>
              if !(isObjectPronoun obj || refersToSelf cardName obj) then none
              else
                (parseCardCount countText).map fun k =>
                  activatedWithCost n costs
                    (.sequence [
                      .defineSelectorVariable n (.owner (.source .this)),
                      .shuffleIntoOwnersLibrary (.source .this),
                      .draw (.variable n) (Value.nat k)])
                    .unlimited
                    (n + 1)

/-- `Return this card from your graveyard to the battlefield attached to target creature you control with power 1 or less.`
The creature is target `n`. `N` is a positive printed power. The card enters
already attached to that creature (CR 303.4f). -/
def parseReturnAttachedPowerAtMost (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (after? (normSentence sentence)
      "return this card from your graveyard to the battlefield attached to ").bind
    fun dest =>
      (split2? dest " with power ").bind fun (targetText, powerText) =>
        (before? powerText " or less").bind positiveCount |>.bind fun p =>
          (parseTargetPhrase targetText).bind fun sel =>
            if sel != permanentWith [.creature] [youControl] then none
            else
              let among :=
                extendIntersection [] sel [.powerAtMost (Value.int (p : Int))]
              some (
                .putOntoBattlefieldInState
                  (.intersection [.inGraveyard, .source .this])
                  [.attachedTo (.target n among)],
                n + 1)

/-- `{2}{W/U}{W/U}: Return this card from your graveyard to the battlefield attached to target creature you control with power 1 or less. Activate only as a sorcery.`
The ability functions in a graveyard (CR 113.6). -/
def parseReturnFromGyAttach (line : String) (n : Nat) : Option (CardPart × Nat) :=
  (splitPrintedAbility? line).bind fun (costText, effect) =>
    match sentences effect with
    | [body, restrict] =>
      if !sentenceIs restrict "activate only as a sorcery" then none
      else
        match parsePrintedCosts "" costText, parseReturnAttachedPowerAtMost body n with
        | some costs, some (action, n') =>
          some (
            .ability (
              .graveyardActivatedIf
                (.timeToCastSorcery (.controller .this))
                costs
                action),
            n')
        | _, _ => none
    | _ => none

/-- `Flashback {4}{W}`. A reminder parenthetical is not rules text (CR 702.34). -/
def parseFlashback (line : String) : Option CardPart :=
  match (after? (normLine line) "flashback ").bind nonemptyMana? with
  | some syms => some (.ability (.keywordWithCost .flashback [.mana syms]))
  | none => none

/-- `Kicker {2}{W}`. A reminder parenthetical is not rules text (CR 702.32). -/
def parseKicker (line : String) : Option CardPart :=
  match (after? (normLine line) "kicker ").bind nonemptyMana? with
  | some syms => some (.ability (.keywordWithCost .kicker [.mana syms]))
  | none => none

/-- `Sneak {1}{B}{B}`. A reminder parenthetical is not rules text. -/
def parseSneak (line : String) : Option CardPart :=
  match (after? (normLine line) "sneak ").bind nonemptyMana? with
  | some syms => some (.ability (.keywordWithCost .sneak [.mana syms]))
  | none => none

/-- `Affinity for Elves` or `Affinity for artifacts` (CR 702.40).
The word after `for` is one plural card type or one subtype plural. -/
def parseAffinity (line : String) : Option CardPart :=
  (after? (normLine line) "affinity for ").bind fun rest =>
    if rest.isEmpty then none
    else
      match cardTypes.find? (fun t => norm (Keyword.affinityPhrase [t] []) == rest) with
      | some t => some (.ability (.keyword (.affinity [t] [])))
      | none =>
        match cardSubtypes.find? (fun st => norm (Keyword.affinityPhrase [] [st]) == rest) with
        | some st => some (.ability (.keyword (.affinity [] [st])))
        | none => none

/-- Creature permanents with flying that this object's controller controls. -/
def flyingCreaturesYouControl : Selector :=
  .intersection [.permanent, .cardType .creature, .keyword .flying, youControl]

/-- Treasure artifacts this object's controller controls. -/
def treasuresYouControl : Selector :=
  .intersection [
    .permanent, .cardType .artifact, .subtype .treasure, youControl]

/-- An attacking creature. -/
def attackingCreatureTarget : Selector :=
  .intersection [.permanent, .cardType .creature, .attacking .all]

/-- `he`, `she`, `it`, `they`, or another reference to this card. -/
def damageSource? (cardName who : String) : Bool :=
  who != "" && (isPersonalPronoun who || refersToSelf cardName who)

/-- `<this> has <keyword> as long as you control another <subtype>.`
This has that keyword while its controller controls another permanent of
that subtype. The subtype is singular. -/
def parseKeywordIfAnother (cardName line keywordText : String) (k : Keyword) :
    Option CardPart :=
  (split2? (normLine line)
      (" has " ++ keywordText ++ " as long as you control another ")).bind
    fun (subject, stText) =>
      if !refersToSelf cardName subject then none
      else
        (subtypeOfOracle? stText).map fun st =>
          .ability (.static (.if
            (.any (anotherSubtypeYouControl st))
            [.gainAbility .this (.keyword k)]))

/-- `<this> has haste as long as you control another Goblin.` -/
def parseHasteIfAnother (cardName line : String) : Option CardPart :=
  parseKeywordIfAnother cardName line "haste" .haste

/-- `Add {B}{R}.` The controller adds that mana. Does not choose a target. -/
def parseAddMana (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "add ").bind nonemptyMana? |>.map fun syms =>
    (.addMana (.controller .this) syms, n)

/-- Cost, one effect sentence, and a trailing activation limit of
`<cost>: <effect>`. -/
def activatedSentence? (cardName line : String) :
    Option (List Cost × String × ActivateLimit) :=
  (splitPrintedAbility? line).bind fun (costText, effect) =>
    let (body, limit) := splitActivateLimit (sentences effect)
    match body, parseActivationCost cardName costText with
    | [one], some costs => some (costs, one, limit)
    | _, _ => none

/-- True when a cost sacrifices another permanent of a printed subtype. -/
def sacrificesAnotherSubtype : List Cost → Bool
  | [] => false
  | .sacrificeCount s 1 :: rest =>
    s.shape.anotherSubtypeYouControl.isSome || sacrificesAnotherSubtype rest
  | _ :: rest => sacrificesAnotherSubtype rest

/-- `{T}, Sacrifice another Goblin: Add {B}{R}.`
Adding mana requires sacrificing another subtype, so `{T}: Add {G}` stays
unrecognized. Also `{2}, {T}: Draw a card, then discard a card.`
An activation limit may follow the effect. -/
def parseActivatedAddOrLoot (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (activatedSentence? cardName line).bind fun (costs, one, limit) =>
    match parseAddMana one n with
    | some (action, n') =>
      if sacrificesAnotherSubtype costs then
        some (activatedWithCost n costs action limit n')
      else none
    | none =>
      match parseDrawThenDiscard one n with
      | some (action, n') => some (activatedWithCost n costs action limit n')
      | none => none

/-- `Whenever <this> attacks, target attacking creature gains first strike until end of turn.`
The attacker is this card. The creature is target `n`. -/
def parseAttackTargetGains (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onAttackN cardName line fun effect =>
    (before? effect " until end of turn").bind (split2? · " gains ") |>.bind
      fun (who, gained) =>
        if who != "target attacking creature" then none
        else
          (parseKeywordPhrase gained).bind fun kws =>
            let effects := gainEffects n attackingCreatureTarget kws
            if effects.isEmpty then none
            else some (.continuous effects .endOfTurn, n + 1)

/-- `This spell costs {X} less to cast, where X is the total power of creatures you control with flying.`
The printed reduction is `{X}`, and X is that total power. It functions on
the stack (CR 604.2). -/
def parseCostLessByFlyingPower (line : String) : Option CardPart :=
  if sentenceIs (normLine line)
      "this spell costs {x} less to cast, where x is the total power of creatures you control with flying" then
    some (.ability (.stackStatic
      (.reduceCostWithX .this [.mana [.x]] (.totalPower flyingCreaturesYouControl))))
  else none

/-- Search for one basic land card, reveal it, and put it into hand.
The found card is variable `n`. -/
def searchBasicLandToHand (n : Nat) : CardAction × Nat :=
  searchRevealToHand n basicLandInLibrary

/-- `When <this> enters, search your library for a basic land card, reveal it, put it into your hand, then shuffle.`
The entering object is this card. The found card is variable `n`. -/
def parseEnterSearchBasicToHand (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onEnterN cardName line fun effect =>
    if sentenceIs effect
        "search your library for a basic land card, reveal it, put it into your hand, then shuffle" then
      some (searchBasicLandToHand n)
    else none

/-- `When <this> enters, it deals 1 damage to any target. If a Dragon is dealt damage this way, destroy it.`
The entering object is this card. The recipient is target `n`, and that
damage is action `n`. The object of the action is destroyed only when the
damage is dealt to it and it has the subtype. -/
def parseEnterDealDamageDestroyIfSubtype (cardName : String) (line : String)
    (n : Nat) : Option (CardPart × Nat) :=
  match sentences line with
  | [enter, cond] =>
    onEnterN cardName enter fun effect =>
      (split2? effect " deals ").bind fun (who, rest) =>
        (split2? rest " damage to ").bind fun (amt, dest) =>
          if !damageSource? cardName who || dest != "any target" then none
          else
            match positiveDigits? amt with
            | none => none
            | some amount =>
              (after? (normSentence cond) "if ").bind dropArticle? |>.bind
                fun rest =>
                  (before? rest " is dealt damage this way, destroy it").bind
                    subtypeOfOracle? |>.map fun st =>
                      (
                        .sequence [
                          .actionId n
                            (.dealDamage (.source .this) (.target n .all)
                              (.nat amount)),
                          .if (.anySubtype (.wasObjectOfAction n) st)
                            [.destroy (.wasObjectOfAction n)]],
                        n + 1)
  | _ => none

/-- `Whenever <this> attacks, he deals damage equal to the number of Treasures you control to any target.`
The attacker is this card. The recipient is target `n`. -/
def parseAttackDamageEqualTreasures (cardName : String) (line : String)
    (n : Nat) : Option (CardPart × Nat) :=
  onAttackN cardName line fun effect =>
    (split2? effect
        " deals damage equal to the number of treasures you control to ").bind
      fun (who, dest) =>
        if !damageSource? cardName who || dest != "any target" then none
        else
          some (
            .dealDamage (.source .this) (.target n .all) (.count treasuresYouControl),
            n + 1)

/-- `Whenever an opponent casts their first noncreature spell each turn, you recruit.`
Recruit is a keyword action of this card's controller. A reminder
parenthetical is not rules text. -/
def parseOpponentFirstNoncreatureRecruit (line : String) : Option CardPart :=
  if sentenceIs (normLine line)
      "whenever an opponent casts their first noncreature spell each turn, you recruit" then
    some (.ability (.triggered
      (.ordinal 1 .turnStart
        (.castSpell (.intersection [
          .spell,
          .not (.cardType .creature),
          .controlled (.opponent (.controller .this))])))
      (.keyword (.controller .this) .recruit)))
  else none

/-- Text after `As long as you have an enduring story,`. -/
def afterEnduringStory? (line : String) : Option String :=
  after? (normLine line) "as long as you have an enduring story, "

/-- This object's controller has an enduring story. -/
def controllerHasEnduringStory : Condition :=
  .enduringStory (.controller .this)

/-- `As long as you have an enduring story, <this> gets +1/+0 and has vigilance.`
A zero bonus is omitted. `+0/+0` with no keywords is not an effect. -/
def parseEnduringStoryGets (cardName line : String) : Option CardPart :=
  (afterEnduringStory? line).bind
    fun rest =>
      (splitGetsOnly? rest).bind fun (who, tail) =>
        if !refersToSelf cardName who then none
        else
          let parsed :=
            match split2? tail " and has " with
            | none => some (tail, ([] : List Keyword))
            | some (pt, has) =>
              (parseKeywordPhrase has).map fun kws => (pt, kws)
          parsed.bind fun (ptText, kws) =>
            match parsePowerToughness ptText with
            | some (p, t) =>
              staticWhile controllerHasEnduringStory
                (flatPowerToughness .this p t ++ keywordGains .this kws)
            | none => none

/-- `As long as you have an enduring story, creatures you control get +1/+1.`
The plural `get` is these creatures, not this card. A zero bonus is omitted.
`+0/+0` is not an effect. -/
def parseEnduringStoryTeamGets (line : String) : Option CardPart :=
  (afterEnduringStory? line).bind fun rest =>
    if (split2? rest " gets ").isSome then none
    else
      (splitGets? rest).bind fun (who, ptText) =>
        match parseControlledPhrase who, parsePowerToughness ptText with
        | some sel, some (p, t) =>
          if sel != creaturesYouControl then none
          else staticWhile controllerHasEnduringStory (flatPowerToughness sel p t)
        | _, _ => none

/-- `As long as you have an enduring story, artifacts and creatures you control have ward {1}.`
`{N}` is a positive generic cost. -/
def parseEnduringStoryTeamWard (line : String) : Option CardPart :=
  (afterEnduringStory? line).bind
    fun rest =>
      (split2? rest " have ward ").bind fun (who, cost) =>
        (genericWard? ("ward " ++ cost)).bind fun n =>
          if who != "artifacts and creatures you control" then none
          else
            staticWhile controllerHasEnduringStory
              [.gainAbility
                (permanentWith [.artifact, .creature] [youControl])
                (.keywordWithCost .ward [.mana [.generic n]])]

/-- `As long as you have an enduring story, creatures can't attack you unless their controller pays {1} for each of those creatures.`
`you` is this object's controller. `{N}` is a positive generic cost. -/
def parseEnduringStoryAttackTax (line : String) : Option CardPart :=
  (afterEnduringStory? line).bind
    fun rest =>
      (between? rest
          "creatures can't attack you unless their controller pays "
          " for each of those creatures").bind
        fun costText =>
          (positiveGeneric? costText).bind fun n =>
            staticWhile controllerHasEnduringStory
              [.cantAttackUnlessPays
                (permanentWith [.creature])
                (.controller .this)
                [.mana [.generic n]]]

/-- `<this> doesn't untap during your untap step unless you have an enduring story.`
The subject is this card. `your` is its controller (CR 502.3). This does not
untap when that player does not have an enduring story. -/
def parseDoesntUntapUnlessEnduringStory (cardName line : String) : Option CardPart :=
  (before? (normLine line)
      " doesn't untap during your untap step unless you have an enduring story").bind
    fun subject =>
      if !refersToSelf cardName subject then none
      else
        staticWhile (.not controllerHasEnduringStory) [.doesntUntap .this]

/-- `Whenever <this> or another nontoken Dwarf you control enters, create a 2/2 red Dwarf creature token.`
The subject is this card. `another` excludes this object. The subtype is
singular. One token uses the singular noun. -/
def parseThisOrNontokenSubtypeEntersCreate (cardName line : String) : Option CardPart :=
  (after? (normLine line) "whenever ").bind fun rest =>
    (split2? rest " or another nontoken ").bind fun (subject, tail) =>
      if !refersToSelf cardName subject then none
      else
        (split2? tail " you control enters, ").bind fun (subtypeText, effect) =>
          match subtypeOfOracle? subtypeText, parseCreateColoredCreatureToken effect with
          | some st, some action =>
            some (.ability (.triggered
              (.or
                (.enter .this)
                (.enter
                  (.intersection [
                    .not .this,
                    .not .token,
                    .permanent,
                    .cardType .creature,
                    .subtype st,
                    youControl])))
              action))
          | _, _ => none

/-- `{1}, {T}, Discard a card: Draw a card.`
Discarding one card is part of the cost. One card is drawn. An activation
limit may follow the effect. -/
def parseActivatedDiscardDraw (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (activatedSentence? cardName line).bind fun (costs, one, limit) =>
    if !costs.any (fun c => c == discardOneCardFromHand) then none
    else
      (parseDrawCards one).map fun action => activatedWithCost n costs action limit n

/-- Cards in this object's controller's hand. -/
def cardsInYourHand : Selector :=
  .intersection [.inHand, .owner (.controller .this)]

/-- Cards in this object's controller's graveyard. -/
def cardsInYourGraveyard : Selector :=
  .intersection [.inGraveyard, .owner (.controller .this)]

/-- `Threshold — This creature gets +1/+1 as long as there are seven or more cards in your graveyard.`
`Threshold` is an ability word (CR 207.2c / 702.62) and may be omitted.
Seven or more cards in your graveyard is that ability. A zero bonus is
omitted. `+0/+0` is not an effect. -/
def parseThresholdGets (cardName line : String) : Option CardPart :=
  let s := withoutAbilityWord (normLine line) "threshold"
  (before? s " as long as there are seven or more cards in your graveyard").bind
    fun pump =>
      (splitGetsOnly? pump).bind fun (who, ptText) =>
        if !refersToSelf cardName who then none
        else
          match parsePowerToughness ptText with
          | some (p, t) =>
            staticWhile
              (.greaterOrEqual (.count cardsInYourGraveyard) 7)
              (flatPowerToughness .this p t)
          | none => none

/-- `Equip abilities you activate that target this creature cost {N} less to activate.`
`{N}` is generic mana, and it is not zero. -/
def parseEquipAbilitiesTargetingThisCostLess (line : String) : Option CardPart :=
  (between? (normLine line)
      "equip abilities you activate that target this creature cost "
      " less to activate").bind positiveGeneric? |>.map fun k =>
    .ability (.static (.reduceCost
      (.intersection [
        Selector.keywordAbility .equip,
        .hasTarget .this,
        youControl])
      [.mana [.generic k]]))

/-- Equip abilities of permanents this object's controller controls. -/
def equipAbilitiesYouControl : Selector :=
  .intersection [Selector.keywordAbility .equip, youControl]

/-- `As long as you have an enduring story, you may pay {0} rather than pay the equip cost of the first equip ability you activate each turn.`
`{0}` is an alternative cost for those Equip abilities (CR 118.9), not a
cost reduction. It applies only while that player has not activated one
since the turn began. Any other mana cost is a different ability. -/
def parseFirstEquipFreeIfEnduringStory (line : String) : Option CardPart :=
  if normLine line ==
      "as long as you have an enduring story, you may pay {0} rather than pay the equip cost of the first equip ability you activate each turn" then
    staticWhile
      (.and
        controllerHasEnduringStory
        (.didNotHappen (.activateAbility equipAbilitiesYouControl) .turnStart))
      [.alternativeCost equipAbilitiesYouControl [.mana [.generic 0]]]
  else none

/-- `Whenever another <subtype> or Equipment you control enters, draw a card. This ability triggers only once each turn.`
The entering permanent is another permanent of that subtype or an Equipment.
One card. The second sentence is the once-each-turn restriction (CR 603.2i). -/
def parseAnotherSubtypeOrEquipmentEntersDraw (line : String) : Option CardPart :=
  match sentences line with
  | [enter, once] =>
    if !sentenceIs once "this ability triggers only once each turn" then none
    else
      (after? (norm enter) "whenever another ").bind fun rest =>
        (before? rest " enters, draw a card").bind fun who =>
          let (obj, controlled) := splitYouControl who
          if !controlled then none
          else
            match parseSubtypeList obj with
            | some [st, .equipment] =>
              some (.ability (.triggered
                (.enter (.intersection [
                  .not .this,
                  .permanent,
                  .union [.subtype st, .subtype .equipment],
                  youControl]))
                (.draw (.controller .this) 1)))
            | _ => none
  | _ => none

/-- `When this creature enters, return up to one other target permanent you control to its owner's hand. If you do, put a +1/+1 counter on this creature.`
Up to one target is zero or one (CR 115.1). That target is `n`, and the return
is action `n`. The counter is put only when that action returns a permanent. -/
def parseEnterReturnOtherPlusOne (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences line with
  | [enter, cond] =>
    if !sentenceIs cond "if you do, put a +1/+1 counter on this creature" then none
    else
      onEnterN cardName enter fun effect =>
        if effect !=
            "return up to one other target permanent you control to its owner's hand" then
          none
        else
          some (
            .sequence [
              .actionId n
                (.returnToHand
                  (.targets n (.range 0 1)
                    (.intersection [.not .this, .permanent, youControl]))),
              .if (.happened (.actionWithId n) .gameStart)
                [.putCounter (.source .this) .plusOnePlusOne 1]],
            n + 1)
  | _ => none

/-- `Equipped creature has <keywords> and can't be blocked.`
The keywords and the restriction are static abilities of this Equipment. -/
def parseEquippedHasAndCantBeBlocked (line : String) : Option (List CardPart) :=
  (after? (normLine line) "equipped creature has ").bind fun rest =>
    (before? rest " and can't be blocked").bind parseKeywordPhrase |>.bind
      fun kws =>
        match kws with
        | [] => none
        | _ =>
          some (
            (kws.map fun k =>
              .ability (.static (.gainAbility (.hostOf .this) (.keyword k)))) ++
            [.ability (.static (.forbid (.block .any (.hostOf .this))))])

/-- `Equip—{cost}, Pay N life.`
The Equip keyword (CR 702.6). The cost is that mana plus `N` life.
`N` is a positive life payment. Equip only as a sorcery. -/
def parseEquipPayLife (line : String) : Option CardPart :=
  (after? (normLine line) "equip—").bind fun rest =>
    match split2? rest ", " with
    | some (costText, lifeText) =>
      match nonemptyMana? costText, parsePayLife lifeText with
      | some syms, some life =>
        some (.ability (.keywordWithCost .equip [.mana syms, .life life]))
      | _, _ => none
    | none => none

/-- `As an additional cost to cast this spell, sacrifice a creature.`
The sacrifice is one creature and is announced at CR 601.2b. The ability
functions while this spell is on the stack (CR 113.6 / 604.2). -/
def parseAdditionalCostSacrificeCreature (line : String) : Option CardPart :=
  if normLine line ==
      "as an additional cost to cast this spell, sacrifice a creature" then
    some (.ability (.stackStatic
      (.additionalCost .this
        [.sacrificeCount (permanentWith [.creature]) 1])))
  else none

/-- `<this> has lifelink as long as you control another Dwarf.` -/
def parseLifelinkIfAnother (cardName line : String) : Option CardPart :=
  parseKeywordIfAnother cardName line "lifelink" .lifelink

/-- A card that is one of two subtypes, e.g. `a Dwarf or Equipment card`. -/
def twoSubtypesCard? (s : String) : Option (CardSubtype × CardSubtype) :=
  (dropArticle? s).bind fun rest =>
    (before? rest " card").bind fun mid =>
      (split2? mid " or ").bind fun (a, b) =>
        match subtypeOfOracle? a, subtypeOfOracle? b with
        | some sa, some sb => some (sa, sb)
        | _, _ => none

/-- Look at the top `k` cards of your library (action `n`). You may reveal one
card of `kind` from among them and put it into your hand (action `n + 1`).
`onBottom` puts the rest on the bottom of that library. -/
def lookAtTopMayRevealToHand (n k : Nat) (kind : Selector)
    (onBottom : Selector → CardAction) : List CardAction :=
  let looked := Selector.wasObjectOfAction n
  let revealed := Selector.wasObjectOfAction (n + 1)
  [
    .actionId n (.lookAt (.topOfLibrary (.controller .this) (.nat k))),
    .optional (.controller .this) (.sequence [
      .actionId (n + 1)
        (.reveal
          (.selected (.controller .this) (.range 1 1)
            (.intersection [looked, kind]))),
      .returnToHand revealed]),
    onBottom (.intersection [looked, .not revealed])]

/-- `When <this> enters, look at the top four cards of your library. You may reveal a Dwarf or Equipment card from among them and put it into your hand. Put the rest on the bottom of your library in a random order.`
The looked-at cards are action `n`. The revealed card is action `n + 1`.
One card uses the singular. The revealed card may also be `a permanent card`. -/
def parseEnterLookAtTopReveal (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences line with
  | [enter, reveal, restBottom] =>
    if !sentenceIs restBottom
        "put the rest on the bottom of your library in a random order" then none
    else
      onEnterN cardName enter fun effect =>
        (after? effect "look at the top ").bind fun tail =>
          (before? tail " of your library").bind topCount? |>.bind fun k =>
            (after? (normSentence reveal) "you may reveal ").bind fun rev =>
              (before? rev " from among them and put it into your hand").bind
                (fun kind =>
                  (twoSubtypesCard? kind).map (fun (a, b) =>
                    Selector.union [.subtype a, .subtype b]) <|>
                  (if kind == "a permanent card" then some .permanent else none))
                |>.map fun kindSel =>
                  (.sequence (lookAtTopMayRevealToHand n k kindSel
                    .putOnLibraryBottomInRandomOrder),
                   n + 2)
  | _ => none

/-- `Create X tapped Treasure tokens, where X is the number of artifacts your opponents control.` -/
def parseCreateTappedTreasuresEqualOppArtifacts (sentence : String) :
    Option CardAction :=
  if sentenceIs sentence
      "create x tapped treasure tokens, where x is the number of artifacts your opponents control" then
    some (.createTokens (.controller .this)
      (.count (.intersection [
        .permanent, .cardType .artifact,
        .controlled (.opponent (.controller .this))]))
      PredefinedToken.treasureToken
      [.tapped])
  else none

/-- `When <this> enters, create X tapped Treasure tokens, where X is the number of artifacts your opponents control.`
X is how many artifact permanents those opponents control. -/
def parseEnterCreateTappedTreasuresEqualOppArtifacts (cardName line : String) :
    Option CardPart :=
  onEnter cardName line parseCreateTappedTreasuresEqualOppArtifacts

/-- Any spell this object's controller casts. -/
def anySpellYouCast : Selector :=
  .intersection [.spell, youControl]

/-- Anything with the Treasure subtype, the source of “mana from a Treasure”. -/
def treasureManaSource : Selector :=
  .subtype .treasure

/-- `Whenever you cast a spell, if mana from a Treasure was spent to cast it, you draw a card and lose 1 life.`
The ability triggers once when that spell is cast, not once for each mana
spent. First, mana from a Treasure — any object with that subtype — is
spent to cast a spell this object's controller casts. That cast is
numbered. Then that spell, argument 1 of the numbered cast, is cast. The
payment happens before the spell becomes cast (CR 601.2h / 601.2i). The
“if” is an intervening if (CR 603.4). One card and 1 life. -/
def parseYouCastSpellIfTreasureDrawLoseLife (line : String) : Option CardPart :=
  (after? (normLine line)
      "whenever you cast a spell, if mana from a treasure was spent to cast it, ").bind
    parseYouDrawCardLoseLife |>.map fun action =>
      .ability (.triggered
        (.sequence [
          .spendManaFrom treasureManaSource
            (.triggerId 1 (.castSpell anySpellYouCast)),
          .castSpell (.wasArgumentOfTrigger 1 1)])
        action)

/-- `Instant and sorcery spells you cast cost {X} less to cast, where X is equipped creature's power.`
The printed reduction is `{X}`. X is the equipped creature's power. -/
def parseInstantSorceryCostLessByEquippedPower (line : String) : Option CardPart :=
  if sentenceIs (normLine line)
      "instant and sorcery spells you cast cost {x} less to cast, where x is equipped creature's power" then
    some (.ability (.static (.reduceCostWithX
      (.intersection [.spell, instantOrSorcery, youControl])
      [.mana [.x]]
      (.greatestPower (.hostOf .this)))))
  else none

/-- Steps of a sequence, in order. A sequence is those steps. -/
def flattenAction : CardAction → List CardAction
  | .sequence as => as.flatMap flattenAction
  | action => [action]

/-! ### Catalog grammar

Phrases of the Hobbit Eternal and Marvel Super Heroes catalog cards. They
are tried after the templates above, so a line those templates read keeps
that reading. -/

/-- A Saga chapter number: `I` through `VI` (CR 714.2). -/
def chapterNumber? (s : String) : Option Nat :=
  match copied s with
  | "I" => some 1
  | "II" => some 2
  | "III" => some 3
  | "IV" => some 4
  | "V" => some 5
  | "VI" => some 6
  | _ => none

/-- The rules text after a leading ability word or flavor word, such as
`Alliance —` or `Seismic Takedown —`. That word has no rules meaning
(CR 207.2c). It is one or more words with no punctuation. A Saga chapter
number is not such a word. The rest keeps its printed case. -/
def afterAbilityWord? (line : String) : Option String :=
  (split2? (rulesText line) " — ").bind fun (word, rest) =>
    if word.isEmpty || rest.isEmpty || (chapterNumber? word).isSome ||
        word.any (fun c => c == ',' || c == '.' || c == ':' || c == '•' || c == '(') then
      none
    else
      match norm word with
      | "ferocious" | "power-up" | "∞" | "infinity" => none
      | "landfall" =>
        if (norm rest).startsWith "whenever a land you control enters, " then some rest else none
      | _ => some rest

/-- A word before the noun of an object description: `attacking`, `tapped`,
`legendary`, `nontoken`, or `non<card type>` such as `nonland`. -/
def objectModifier? (w : String) : Option Selector :=
  match w with
  | "attacking" => some (.attacking .all)
  | "tapped" => some .tapped
  | "legendary" => some (.supertype .legendary)
  | "basic" => some (.supertype .basic)
  | "nontoken" => some (.not .token)
  | "untapped" => some (.not .tapped)
  | "nonlegendary" => some (.not (.supertype .legendary))
  | _ => (after? w "non").bind typeOfOracle? |>.map fun t => .not (.cardType t)

/-- Leading modifier words and the words after them. -/
def splitModifiers : List String → List Selector × List String
  | [] => ([], [])
  | w :: rest =>
    match objectModifier? w with
    | some sel =>
      if rest.isEmpty then ([], [w])
      else
        let (mods, core) := splitModifiers rest
        (sel :: mods, core)
    | none => ([], w :: rest)

/-- A subtype printed singular (`Wolf`) or plural (`Goblins`, `Wolves`). -/
def subtypeWord? (w : String) : Option CardSubtype :=
  subtypeOfOracle? w <|> pluralCreatureType? w <|> amassSubtype? w

/-- Subtypes joined by `and`, `or`, or commas: `Goblins and Orcs`. -/
def subtypeWords? (s : String) : Option (List CardSubtype) :=
  let parts := orList ((norm s).replace " and " " or ")
  if parts.isEmpty then none else parts.mapM subtypeWord?

/-- Subtypes that are not creature types (CR 205.3g-205.3m). -/
def nonCreatureSubtypes : List CardSubtype := [
  .adventure, .arcane, .aura, .clue, .equipment, .food, .forest, .gate, .island,
  .mountain, .plains, .plan, .saga, .swamp, .treasure, .vehicle]

/-- The noun of an object description. `permanent` has no type. A card type
list is those types; `creature token` is also a token. A subtype list is
those subtypes, and `withCreature` adds the creature type to a subtype
list. The second result is whether the noun names tokens. -/
def objectNoun? (core : String) (withCreature : Bool) :
    Option (List Selector × Bool) :=
  let core := norm core
  let (core, tokens) :=
    match before? core " tokens" <|> before? core " token" with
    | some rest => (rest, true)
    | none => (core, false)
  if core == "token" || core == "tokens" then some ([], true)
  else if core == "permanent" || core == "permanents" then some ([], tokens)
  else
    match typesInPhrase core with
    | some ts => some ([selectorOfTypes ts], tokens)
    | none =>
      ((subtypeWords? core).map fun sts =>
        let creature := withCreature && !sts.any nonCreatureSubtypes.contains
        ((if creature then [.cardType .creature] else []) ++ [subtypeSelector sts],
          tokens)) <|>
      ((before? core " creatures" <|> before? core " creature").bind subtypeWords? |>.bind fun sts =>
        if sts.any nonCreatureSubtypes.contains then none
        else some ([.cardType .creature, subtypeSelector sts], tokens))

/-- A trailing `with power N or less` or `with power N or greater`, and the
text before it. -/
def splitPowerClause (s : String) : String × List Selector :=
  match split2? s " with power " with
  | some (rest, clause) =>
    match (before? clause " or less").bind natOfDigits?,
        (before? clause " or greater").bind natOfDigits? |>.filter (· != 0) with
    | some k, _ => (rest, [.powerAtMost (Value.int k)])
    | _, some k => (rest, [.powerAtLeast (Value.int k)])
    | none, none => (s, [])
  | none => (s, [])

/-- The controller clause after an object description, and the text before it. -/
def splitControllerClause (s : String) : String × List Selector :=
  match before? s " you control" with
  | some rest => (rest, [youControl])
  | none =>
    match before? s " an opponent controls" <|> before? s " your opponents control" with
    | some rest => (rest, [.controlled (.opponent (.controller .this))])
    | none => (s, [])

/-- A trailing `with <keyword>` or `without <keyword>`, and the text before it. -/
def splitKeywordClause (s : String) : String × List Selector :=
  match split2? s " without " with
  | some (rest, kw) =>
    match keywordOfOracle? kw with
    | some k => (rest, [.not (.keyword k)])
    | none => (s, [])
  | none =>
    match split2? s " with " with
    | some (rest, kw) =>
      match keywordOfOracle? kw with
      | some k => (rest, [.keyword k])
      | none => (s, [])
    | none => (s, [])

/-- The objects matching every selector. One selector is itself. -/
def intersectionOf : List Selector → Selector
  | [one] => one
  | many => .intersection many

/-- A permanent described by `another`, modifiers, a noun, `with` or
`without` a keyword, and a controller: `another nontoken Hero you control`,
`attacking creature tokens you control`, `nonland, nontoken permanent`, or
`noncreature artifact or noncreature enchantment`. `another` and `other`
exclude this object. `withCreature` adds the creature type to a subtype.
Supertypes are last. -/
def parseObjectDesc (s : String) (withCreature : Bool) : Option Selector :=
  let s := norm s
  let (s, other) :=
    match after? s "another " <|> after? s "other " with
    | some rest => (rest, true)
    | none => (s, false)
  let (s, power) := splitPowerClause s
  let (s, controller) := splitControllerClause s
  let (s, keywords) := splitKeywordClause s
  let words := (s.replace ", " " ").splitOn " " |>.map copied |>.filter (· != "")
  let (mods, coreWords) := splitModifiers words
  let modWords := words.take mods.length
  let core := String.intercalate " " coreWords
  let core := modWords.foldl (fun c w => c.replace (" or " ++ w ++ " ") " or ") core
  (objectNoun? core withCreature).map fun (noun, tokens) =>
    let isTokenNeg := fun (sel : Selector) => sel == .not .token
    let isTypeNeg := fun (sel : Selector) =>
      match sel with
      | .not (.cardType _) => true
      | _ => false
    let isSupertype := fun (sel : Selector) =>
      match sel with
      | .supertype _ => true
      | _ => false
    let rest := mods.filter fun m => !isTokenNeg m && !isTypeNeg m && !isSupertype m
    intersectionOf (
      (if other then [.not .this] else []) ++
      mods.filter isTokenNeg ++
      [.permanent] ++
      mods.filter isTypeNeg ++
      noun ++
      (if tokens then [.token] else []) ++
      rest ++
      keywords ++
      controller ++
      mods.filter isSupertype ++
      power)

/-- `you control a legendary creature`, `you control a Goblin or Orc`: the
object phrase after `you control`, as a condition. -/
def youControlCondition? (obj : String) : Option Condition :=
  (dropArticle? obj).bind (parseObjectDesc · false) |>.map fun sel =>
    .any (andYouControl sel)

/-- A permanent phrase the way a target names it: a subtype is a creature
of that subtype. -/
def parseTargetObject (s : String) : Option Selector :=
  parseObjectDesc s true

/-- `target <object>`, `another target <object>`, `up to one target <object>`,
`up to one other target <object>`, `each of up to two target <object>`, or
`any target`, as target `n`. Up to N is zero through N (CR 115.1). `other`
excludes this object. `any target` is a player or a permanent that can be
dealt damage. -/
def parseTargetDesc (s : String) (n : Nat) : Option Selector :=
  let s := norm s
  if s == "any target" then some (.target n .all)
  else
    let upTo :=
      (after? s "each of up to " <|> after? s "up to ").bind fun rest =>
        (split2? rest " target ").bind fun (countText, obj) =>
          let (countText, obj) :=
            match before? countText " other" with
            | some c => (c, "other " ++ obj)
            | none => (countText, obj)
          (positiveCount countText).bind fun k =>
            (parseTargetObject obj).map fun sel => .targets n (.range 0 (Value.nat k)) sel
    let another :=
      (after? s "another target ").bind fun obj =>
        (parseTargetObject ("another " ++ obj)).map fun sel => .target n sel
    let plain :=
      (after? s "target ").bind fun obj =>
        (parseTargetObject obj).map fun sel => .target n sel
    upTo <|> another <|> plain

/-- A card in your graveyard: `creature card` or `artifact or enchantment card`. -/
def parseGraveyardCard (s : String) : Option Selector :=
  (before? (norm s) " card").bind (fun kind =>
    ((typesInPhrase kind).map selectorOfTypes) <|> ((subtypeOfOracle? kind).map .subtype)) |>.map
    fun k => .intersection [.inGraveyard, k, .owner (.controller .this)]

/-- The trigger or the spell's controller plays each keyword action: `it`,
`he`, `she`, or this card's name is this object. -/
def selfSubject? (cardName who : String) : Option Selector :=
  if damageSource? cardName who then some (.source .this) else none

/-- Actions from a sentence parser as one action. One action is itself;
several are a sequence, with inner sequences flattened. -/
def combineActions (actions : List CardAction) : Option CardAction :=
  match actions.flatMap flattenAction with
  | [] => none
  | [one] => some one
  | many => some (.sequence many)

/-- Keywords gained by `sel` until end of turn. -/
def gainUntilEnd (sel : Selector) (kws : List Keyword) : Option CardAction :=
  if kws.isEmpty then none
  else some (.continuous (keywordGains sel kws) .endOfTurn)

/-- A subject that gets or gains something: a target (numbered `n`), this
card, `it` (the previous target), `that creature` (the previous target),
`enchanted creature`, `equipped creature`, or permanents such as
`creatures you control`. The number is the next one after the subject. -/
def parseSubject (cardName who : String) (n : Nat) : Option (Selector × Nat) :=
  let who := norm who
  match who with
  | "it" | "that creature" =>
    if n <= 1 then none else some (.targetReference (n - 1), n)
  | "he" | "she" => some (.source .this, n)
  | "enchanted creature" | "equipped creature" => some (.hostOf .this, n)
  | "all creatures" => some (permanentWith [.creature], n)
  | _ =>
    if refersToSelf cardName who then some (.source .this, n)
    else
      match parseTargetDesc who n with
      | some sel => some (sel, n + 1)
      | none => (parseObjectDesc who false).map (·, n)

/-- `<subject> get(s) +P/+T [and gain(s) <keywords>] until end of turn`.
The first effect declares a target in the subject; later ones refer to it.
A zero bonus is omitted. -/
def parseGetsGainsUntilEnd (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (before? (normSentence sentence) " until end of turn").bind fun body =>
    (splitGets? body).bind fun (who, rest) =>
      let (ptText, kws?) :=
        match split2? rest " and gains " <|> split2? rest " and gain " with
        | some (pt, gained) => (pt, parseKeywordPhrase gained)
        | none => (rest, some [])
      match parseSubject cardName who n, parsePowerToughness ptText, kws? with
      | some (sel, n'), some (p, t), some kws =>
        let pt := flatPowerToughness sel p t
        let later := if pt.isEmpty then sel else sel.referenceTargets
        let effects := pt ++ keywordGains later kws
        if pt.isEmpty then none
        else some (.continuous effects .endOfTurn, n')
      | _, _, _ => none

/-- `<subject> gain(s) <keywords> until end of turn [and can't be blocked this turn]`.
The keywords, and the blocking restriction, last until end of turn. -/
def parseGainUntilEnd (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  let s := normSentence sentence
  let (s, unblockable) :=
    match before? s " and can't be blocked this turn" with
    | some rest => (rest, true)
    | none => (s, false)
  (before? s " until end of turn").bind fun body =>
    (split2? body " gains " <|> split2? body " gain ").bind fun (who, gained) =>
      match parseSubject cardName who n, parseKeywordPhrase gained with
      | some (sel, n'), some (k :: ks) =>
        let first := ContinuousEffect.gainAbility sel (.keyword k)
        let later := keywordGains sel.referenceTargets ks
        let block :=
          if unblockable then [ContinuousEffect.forbid (.block .any sel.referenceTargets)]
          else []
        some (.continuous (first :: later ++ block) .endOfTurn, n')
      | _, _ => none

/-- `Put <count> +1/+1 counter(s) on <who>`: a target, `each of up to two target
creatures`, `each other creature you control`, or this card. -/
def parsePutCountersOn (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (parsePutPlusOneOn? sentence).bind fun (k, who) =>
    let who := norm who
    let onEach :=
      (after? who "each ").bind fun each =>
        if (after? each "of ").isSome then none
        else (parseObjectDesc each false).map fun sel => (.putCounter sel .plusOnePlusOne (.nat k), n)
    let onTarget :=
      (parseTargetDesc ((after? who "each of ").getD who) n).map fun sel =>
        (.putCounter sel .plusOnePlusOne (.nat k), n + 1)
    let onSelf :=
      if refersToSelf cardName who || who == "it" then
        some (.putCounter (.source .this) .plusOnePlusOne (.nat k), n)
      else none
    onSelf <|> onEach <|> onTarget

/-- `create <count> [tapped] <P>/<T> <color> <subtypes> creature token(s)
[with <keywords>]`. One token uses the singular noun; more than one uses the
plural. `X` is the value of X (CR 107.3) and uses the plural. A tapped token
enters tapped (CR 110.5). The token is a creature of that power, toughness,
color, and subtypes, with those keywords. The color may be `colorless`, and
the type `artifact creature`. -/
def parseCreateCreatureTokens (sentence : String) : Option CardAction :=
  (after? (normSentence sentence) "create ").bind fun rest =>
    let (rest, kws?) :=
      match split2? rest " with " with
      | some (head, kwText) => (head, parseKeywordPhrase kwText)
      | none => (rest, some [])
    let words := rest.splitOn " " |>.map copied |>.filter (· != "")
    match words with
    | countText :: more =>
      let (tapped, more) :=
        match more with
        | "tapped" :: after => (true, after)
        | _ => (false, more)
      match more with
      | pt :: colorText :: typeWords =>
        match typeWords.reverse with
        | tokenWord :: "creature" :: subtypeWordsRev =>
          let plural := tokenWord == "tokens"
          let count? : Option Value :=
            if countText == "x" then (if plural then some .x else none)
            else (nounCount? countText plural).map Value.nat
          let (types, subtypeWordsRev) : List CardType × List String :=
            match subtypeWordsRev with
            | "artifact" :: more => ([.artifact, .creature], more)
            | _ => ([.creature], subtypeWordsRev)
          let colors? : Option (List Color) :=
            if colorText == "colorless" then some [] else (colorName? colorText).map ([·])
          if tokenWord != "token" && !plural then none
          else
            match count?, parseUnsignedPT pt, colors?,
                subtypeWordsRev.reverse.mapM subtypeOfOracle?, kws? with
            | some k, some (p, t), some cs, some (st :: sts), some kws =>
              some (.createTokens (.controller .this) k
                (types.map CardPart.type ++ (st :: sts).map CardPart.subtype ++
                  [.colorIndicator cs, .power p, .toughness t] ++
                  kws.map fun kw => .ability (.keyword kw))
                (if tapped then [.tapped] else []))
            | _, _, _, _, _ => none
        | _ => none
      | _ => none
    | [] => none

/-- `Create a Treasure token`, `create two Treasure tokens`, `create X
Treasure tokens`, `create a Food token`, or `create a Food token or a
Treasure token`. Food and Treasure are predefined tokens (CR 111.10). `X`
takes the plural noun and is the X of the cost (CR 107.3). With `or`, the
player chooses one to create. -/
def parseCreatePredefinedTokens (sentence : String) : Option CardAction :=
  let one (s : String) : Option CardAction :=
    (after? (norm s) "create ").bind fun rest =>
      let (countText, noun) :=
        match rest.splitOn " " with
        | c :: more => (copied c, copied (String.intercalate " " more))
        | [] => ("", rest)
      let named :=
        (before? noun " tokens").map (true, ·) <|> (before? noun " token").map (false, ·)
      named.bind fun (plural, kind) =>
        let count? : Option Value :=
          if countText == "x" then (if plural then some .x else none)
          else (nounCount? countText plural).map Value.nat
        count?.bind fun k =>
          let parts? : Option (List CardPart) :=
            match kind with
            | "treasure" => some PredefinedToken.treasureToken
            | "food" => some PredefinedToken.foodToken
            | _ => none
          parts?.map fun parts => .createTokens (.controller .this) k parts
  let s := normSentence sentence
  match split2? s " or a " with
  | some (first, second) =>
    match one first, one ("create a " ++ second) with
    | some a, some b => some (.playerSelectAction (.controller .this) (.range 1 1) [a, b])
    | _, _ => none
  | none => one s

/-- `<this card> deals N damage to <recipient>`: any target, target opponent,
each opponent, or each creature blocking it. The source is this object.
`N` is a positive printed number. -/
def parseDealsDamageTo (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " deals ").bind fun (who, rest) =>
    if !damageSource? cardName who then none
    else
      (split2? rest " damage to ").bind fun (amt, dest) =>
        (positiveDigits? amt).bind fun amount =>
          let recipient : Option (Selector × Nat) :=
            match dest with
            | "each opponent" => some (.opponent (.controller .this), n)
            | "target opponent" => some (.target n (.opponent (.controller .this)), n + 1)
            | "each creature blocking it" => some (.blocking .this, n)
            | _ => (parseTargetDesc dest n).map (·, n + 1)
          recipient.map fun (sel, n') => (.dealDamage .this sel (.nat amount), n')

/-- `This Saga deals X damage to target opponent, where X is the greatest mana
value among artifacts you control.` The opponent is target `n`. -/
def parseDealsGreatestManaValueDamage (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " deals x damage to target opponent, where x is the greatest mana value among ").bind
    fun (who, among) =>
      if !damageSource? cardName who then none
      else
        (parseObjectDesc among false).map fun sel =>
          (.dealDamage .this (.target n (.opponent (.controller .this)))
            (.greatestManaValue sel), n + 1)

/-- `It deals damage equal to its power to target creature an opponent controls.`
The source is this object. The recipient is target `n`. -/
def parseSelfDealsDamageEqualToPower (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " deals damage equal to its power to ").bind
    fun (who, dest) =>
      if !damageSource? cardName who then none
      else
        (parseTargetDesc dest n).map fun sel => (.dealDamageEqualToPower .this sel, n + 1)

/-- `<this card> deals 3 damage divided as you choose among one, two, or three
targets.` Its controller divides the damage (CR 601.2d). The counts are a
positive contiguous range of any targets, numbered `n`. -/
def parseDealsDividedDamage (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (before? (normSentence sentence) " targets").bind fun body =>
    (split2? body " deals ").bind fun (who, rest) =>
      if !damageSource? cardName who then none
      else
        (split2? rest " damage divided as you choose among ").bind fun (amt, counts) =>
          match positiveCount amt, parseContiguousCounts counts with
          | some amount, some (lo, hi) =>
            some (
              .divideDamage (.controller .this) .this
                (.targets n (.range (Value.nat lo) (Value.nat hi)) .all)
                (Value.nat amount),
              n + 1)
          | _, _ => none

/-- `Tap <target>` or `Untap <target>`. `Untap that creature` is the previous
target. -/
def parseTapOrUntap (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := normSentence sentence
  let tap := (after? s "tap ").bind fun who => (parseTargetDesc who n).map fun sel => (.tap sel, n + 1)
  let untap :=
    (after? s "untap ").bind fun who =>
      if who == "that creature" then
        if n <= 1 then none else some (.untap (.targetReference (n - 1)), n)
      else (parseTargetDesc who n).map fun sel => (.untap sel, n + 1)
  tap <|> untap

/-- `Destroy <target>`. -/
def parseDestroyTarget (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "destroy ").bind fun who =>
    (parseTargetDesc who n).map fun sel => (.destroy sel, n + 1)

/-- `Return <target card> from your graveyard to your hand`, or
`Return <target> to its owner's hand`. A spell is on the stack. -/
def parseReturnToHand (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := normSentence sentence
  let fromGraveyard :=
    (between? s "return target " " from your graveyard to your hand").bind parseGraveyardCard |>.map
      fun sel => (.returnToHand (.target n sel), n + 1)
  let toOwner :=
    (between? s "return " " to its owner's hand").bind fun who =>
      if who == "target spell" then some (.returnToHand (.target n .spell), n + 1)
      else (parseTargetDesc who n).map fun sel => (.returnToHand sel, n + 1)
  fromGraveyard <|> toOwner

/-- `Surveil N`. Does not choose a target. -/
def parseSurveil (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "surveil ").bind positiveCount |>.map fun k =>
    (.surveil (.controller .this) (Value.nat k), n)

/-- `<who> connive(s)`: this object with `it`, `he`, `she`, or its name, or
`up to one target creature you control`. Connive is a keyword action of that
object (CR 701.50). -/
def parseConnive (cardName sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := normSentence sentence
  (before? s " connives" <|> before? s " connive").bind fun who =>
    match selfSubject? cardName who with
    | some sel => some (.keyword sel (.connive (.nat 1)), n)
    | none => (parseTargetDesc who n).map fun sel => (.keyword sel (.connive (.nat 1)), n + 1)

/-- `Discard a card.` / `Discard two cards.` The player is this spell's
controller. One card is singular. More than one is plural. -/
def parseDiscardCards (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "discard ").bind parseCardCount |>.map fun k =>
    (.discard (.controller .this) (Value.nat k), n)

/-- `Draw <count>`, or `You draw <count> and lose N life`. -/
def parseDrawAndLoseLife (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := normSentence sentence
  let lose :=
    (after? s "you draw ").bind (split2? · " and lose ") |>.bind fun (drawText, lifeText) =>
      match parseCardCount drawText, lifeAmount? ("lose " ++ lifeText) "lose " with
      | some k, some life =>
        some (.sequence [
          .draw (.controller .this) (Value.nat k),
          .loseLife (.controller .this) (Value.nat life)], n)
      | _, _ => none
  lose <|> unchanged (parseDrawCards s) n

/-- `Each opponent loses N life`, `you lose N life`, or
`target opponent loses N life`. The target is numbered `n`. -/
def parseLoseLife (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := normSentence sentence
  ((parseEachOpponentLosesLife s).map fun k =>
      (.loseLife (.opponent (.controller .this)) (Value.nat k), n)) <|>
    ((lifeAmount? s "you lose ").map fun k =>
      (.loseLife (.controller .this) (Value.nat k), n)) <|>
    ((lifeAmount? s "target opponent loses ").map fun k =>
      (.loseLife (.target n (.opponent (.controller .this))) (Value.nat k), n + 1))

/-- `Target player mills <count>`. The player is target `n`. -/
def parseTargetPlayerMills (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "target player mills ").bind parseCardCount |>.map fun k =>
    (.mill (.target n .player) (Value.nat k), n + 1)

/-- `Each player sacrifices a creature of their choice.` Each player, bound to
variable `n`, chooses one creature they control to sacrifice (CR 701.17a). -/
def parseEachPlayerSacrifices (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (between? (normSentence sentence) "each player sacrifices " " of their choice").bind
    dropArticle? |>.bind typesInPhrase |>.map fun ts =>
      (.forEachVariable n .player [
        .sacrifice
          (.selected (.variable n) (.range 1 1)
            (permanentWith ts [.controlled (.variable n)]))],
       n + 1)

/-- `Search your library for a basic land card, put that card onto the
battlefield tapped, then shuffle`, or `Search your library for a <subtype>
card, reveal it, put it into your hand, then shuffle`. The found card is
variable `n` when it is revealed. -/
def parseSearchLibrary (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := normSentence sentence
  let tapped :=
    if s == "search your library for a basic land card, put that card onto the battlefield tapped, then shuffle" then
      parseSearchBasicLandTapped
        "search your library for a basic land card, put it onto the battlefield tapped, then shuffle" n
    else none
  let reveal :=
    (between? s "search your library for " " card, reveal it, put it into your hand, then shuffle").bind
      dropArticle? |>.bind fun kind =>
        if kind == "basic land" then some (searchRevealToHand n basicLandInLibrary)
        else
          (subtypeOfOracle? kind).map fun st =>
            searchRevealToHand n (.intersection [.inLibrary, .subtype st])
  tapped <|> reveal

/-- `<who> fights up to one other target creature`. This object fights that
creature (CR 701.12). -/
def parseSelfFights (cardName sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " fights ").bind fun (who, dest) =>
    if !damageSource? cardName who then none
    else
      let dest := (dest.replace "one other target" "one target another")
      (after? dest "up to one target ").bind parseTargetObject |>.map fun sel =>
        (.fight .this (.targets n (.range 0 1) sel), n + 1)

/-- `Exile <targets>, then return them to the battlefield tapped under their
owner's control.` Also `return that card … under its owner's control`. The
exile is action `n`. The exiled cards return tapped under their owner's
control. -/
def parseExileThenReturnTapped (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := normSentence sentence
  let parsed :=
    (before? s ", then return them to the battlefield tapped under their owner's control") <|>
      (before? s ", then return that card to the battlefield tapped under its owner's control")
  parsed.bind (after? · "exile ") |>.bind fun who =>
    (parseTargetDesc who n).map fun sel =>
      (.sequence [
        .actionId n (.exile sel),
        .putOntoBattlefieldInState
          (.wasCreatedByAction n)
          [.tapped, .controlled (.owner (.wasCreatedByAction n))]],
       n + 1)

/-- `Exile <targets>, then return that card to the battlefield under its owner's control.`
The exile is action `n`. The card returns untapped under its owner's control. -/
def parseExileThenReturn (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := normSentence sentence
  (before? s ", then return that card to the battlefield under its owner's control").bind
    (after? · "exile ") |>.bind fun who =>
      (parseTargetDesc who n).map fun sel =>
        (.sequence [
          .actionId n (.exile sel),
          .putOntoBattlefieldInState
            (.wasCreatedByAction n)
            [.controlled (.owner (.wasCreatedByAction n))]],
         n + 1)

/-- `Creatures without flying can't block this turn.` Only creatures block,
so the blockers are objects without that keyword. -/
def parseWithoutKeywordCantBlock (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (between? (normSentence sentence) "creatures without " " can't block this turn").bind
    keywordOfOracle? |>.map fun k =>
      (.continuous [.forbid (.block (.not (.keyword k)) .all)] .endOfTurn, n)

/-- `Then discard two cards unless you discard an artifact card.` Discarding
an artifact card is the cost that prevents discarding that many cards. -/
def parseDiscardUnlessArtifact (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (between? (normSentence sentence) "discard " " unless you discard an artifact card").bind
    parseCardCount |>.map fun k =>
      (.preventable (.controller .this) [.discard (.cardType .artifact)]
        (.discard (.controller .this) (Value.nat k)), n)

/-- `Artifact spells you cast this turn cost {1} less to cast.` That many
generic mana less until end of turn. -/
def parseSpellsCostLessThisTurn (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " spells you cast this turn cost ").bind fun (kind, rest) =>
    match typeOfOracle? kind, (before? rest " less to cast").bind positiveGeneric? with
    | some t, some k =>
      some (.continuous
        [.reduceCost (.intersection [.spell, .cardType t, youControl]) [.mana [.generic k]]]
        .endOfTurn, n)
    | _, _ => none

/-- `If you control another Hero, you gain 2 life.` or `If you control another
Hero, Human Torch deals 1 damage to target opponent.` `another` excludes this
object. The condition is checked on resolution. -/
def parseIfControlAnotherGainLife (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (after? (normSentence sentence) "if you control another ").bind (split2? · ", ") |>.bind
    fun (stText, effect) =>
      match subtypeOfOracle? stText,
          parseYouGainLife effect n <|> parseDealsDamageTo cardName effect n with
      | some st, some (action, n') => some (.if (.any (anotherSubtypeYouControl st)) [action], n')
      | _, _ => none

/-- `Each opponent discards a card.` Each opponent chooses the card. -/
def parseEachOpponentDiscards (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "each opponent discards ").bind parseCardCount |>.map fun k =>
    (.discard (.opponent (.controller .this)) (Value.nat k), n)

/-- `Draw a card if her power is 4 or greater.` The power is this object's,
checked on resolution. -/
def parseDrawIfPowerAtLeast (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " if ").bind fun (draw, cond) =>
    (after? draw "draw ").bind parseCardCount |>.bind fun k =>
      (between? cond "" " or greater").bind (split2? · " power is ") |>.bind fun (who, p) =>
        let who := (before? who "'s").getD
          (match who with
            | "his" | "her" | "its" => "it"
            | _ => "")
        if !damageSource? cardName who then none
        else
          (positiveDigits? p).map fun p =>
            (.if (.any (.intersection [.source .this, .powerAtLeast (Value.int p)]))
              [.draw (.controller .this) (Value.nat k)], n)

/-- `You gain N life for each <objects>.` Each of those objects is variable `n`. -/
def parseGainLifeForEach (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " life for each ").bind fun (gain, each) =>
    match (after? gain "you gain ").bind positiveCount, parseObjectDesc each false with
    | some k, some sel =>
      some (.forEachVariable n sel [.gainLife (.controller .this) (Value.nat k)], n + 1)
    | _, _ => none

/-- `Target player gains 2 life, then searches their library for a basic land
card, puts it onto the battlefield tapped, then shuffles.` The player is target
`n`, and that player searches. -/
def parseTargetGainsThenSearchesBasic (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (between? (normSentence sentence) "target player gains "
      " life, then searches their library for a basic land card, puts it onto the battlefield tapped, then shuffles").bind
    positiveCount |>.map fun k =>
      (.sequence [
        .gainLife (.target n .player) (Value.nat k),
        .searchLibraryThenShuffle (.targetReference n) [
          .putOntoBattlefieldInState
            (.selected (.targetReference n) (.range 1 1) basicLandInLibrary)
            [.tapped]]],
       n + 1)

/-- `The owner of target creature an opponent controls puts it into their
library second from the top or on the bottom.` That owner chooses where.
The creature is target `n`. -/
def parseOwnerPutsSecondOrBottom (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (between? (normSentence sentence) "the owner of "
      " puts it into their library second from the top or on the bottom").bind
    fun who =>
      (parseTargetDesc who n).map fun sel =>
        (.playerSelectAction (.owner (.targetReference n)) (.range 1 1) [
          .putIntoLibraryFromTop sel 2,
          .putOnBottomOfLibrary (.targetReference n)],
         n + 1)

/-- `attach it to <target>`, or `attach <target> to <target>`. `it` or this
card is the attachment. -/
def parseCatalogAttach (cardName sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "attach ").bind (fun s =>
      match (s.splitOn " to ").reverse with
      | dest :: whatRev@(_ :: _) =>
        some (copied (String.intercalate " to " whatRev.reverse), copied dest)
      | _ => none) |>.bind fun (what, dest) =>
    if what == "it" || refersToSelf cardName what then
      (parseTargetDesc dest n).map fun sel => (.attach .this sel, n + 1)
    else
      (parseTargetDesc what n).bind fun attached =>
        (parseTargetDesc dest (n + 1)).map fun host => (.attach attached host, n + 2)

/-- `<target> can't be blocked this turn except by creatures with <keyword>.`
Only creatures with that keyword may block it until end of turn. -/
def parseCantBeBlockedExceptBy (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " can't be blocked this turn except by creatures with ").bind
    fun (who, kw) =>
      match parseTargetDesc who n, keywordOfOracle? kw with
      | some sel, some k =>
        some (.continuous [.forbid (.block (.not (.keyword k)) sel)] .endOfTurn, n + 1)
      | _, _ => none

/-- `Until end of turn, <subject> gains "<ability>".` The quoted text is a
triggered ability of that object (CR 113.10); `this creature` in it is that
object. -/
def parseGainsQuotedUntilEnd (cardName sentence : String) (n : Nat)
    (quoted : String → Option Ability) : Option (CardAction × Nat) :=
  let s := copied sentence
  let s := (before? s ".").getD s
  (after? (norm s) "until end of turn, ").bind fun _ =>
    (split2? ((s.drop "until end of turn, ".length).copy) " gains \"").bind fun (who, rest) =>
      (before? rest "\"").bind fun text =>
        match parseSubject cardName who n, quoted text with
        | some (sel, n'), some ability => some (.continuous [.gainAbility sel ability] .endOfTurn, n')
        | _, _ => none

/-- Mixed card types and subtypes joined by `or`: `Hero or enchantment`. -/
def typeOrSubtypeList? (s : String) : Option Selector :=
  let parts := orList s
  if parts.isEmpty then none
  else
    (parts.mapM fun w =>
        (if w == "permanent" then some Selector.permanent else none) <|>
        ((typeOfOracle? w).map Selector.cardType) <|> ((subtypeOfOracle? w).map Selector.subtype)) |>.map
      fun
        | [one] => one
        | many => .union many

/-- `Two target players each draw a card.` The players are targets `n`. -/
def parseTwoTargetPlayersEachDraw (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "two target players each draw ").bind parseCardCount |>.map
    fun k => (.draw (.targets n (.range 2 2) .player) (Value.nat k), n + 1)

/-- `create a 3/1 colorless Wall artifact creature token with defender named
Stone Boulder`. The token has that name as printed (CR 111.4). -/
def parseCreateNamedCreatureTokens (sentence : String) : Option CardAction :=
  (split2? (stripTrailingPeriod sentence) " named ").bind fun (head, tokenName) =>
    (parseCreateCreatureTokens head).bind fun
      | .createTokens who k parts states => some (.createTokens who k (.name tokenName :: parts) states)
      | _ => none

/-- A single token to create: `a Treasure token` or `a 1/1 green Elf creature
token`. -/
def createOneToken? (s : String) : Option CardAction :=
  match parseCreatePredefinedTokens s <|> parseCreateCreatureTokens s with
  | some a@(.createTokens _ (.nat 1) _ _) => some a
  | _ => none

/-- `create a Treasure token for each Villain you control`. One token for each
matching object; the object is variable `n`. -/
def parseCreateTokensForEach (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " for each ").bind fun (create, each) =>
    match createOneToken? create, parseObjectDesc each false with
    | some token, some sel => some (.forEachVariable n sel [token], n + 1)
    | _, _ => none

/-- `Look at the top twenty cards of your library, put any number of land cards
from among them onto the battlefield tapped, then shuffle.` The look is action
`n`. The lands are put onto the battlefield from the library before it is
shuffled. -/
def parseLookTopPutLandsShuffle (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (between? (normSentence sentence) "look at the top "
      " cards of your library, put any number of land cards from among them onto the battlefield tapped, then shuffle").bind
    (fun c => (twentyOrSmall? c)) |>.map fun k =>
      (.sequence [
        .actionId n (.lookAt (.topOfLibrary (.controller .this) (Value.nat k))),
        .searchLibraryThenShuffle (.controller .this) [
          .putOntoBattlefieldInState
            (.selected (.controller .this) .any
              (.intersection [.wasObjectOfAction n, .cardType .land]))
            [.tapped]]], n + 1)
where
  twentyOrSmall? (s : String) : Option Nat :=
    if s == "twenty" then some 20 else positiveCount s

/-- `add {R} for each artifact your opponents control`. The mana is added once
for each matching object; the object is variable `n`. -/
def parseAddManaForEach (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " for each ").bind fun (add, each) =>
    match (after? add "add ").bind nonemptyMana?, parseObjectDesc each false with
    | some syms, some sel =>
      some (.forEachVariable n sel [.addMana (.controller .this) syms], n + 1)
    | _, _ => none

/-- `add two mana in any combination of {U}, {B}, and/or {R}` (CR 106.4). -/
def parseAddManaInAnyCombination (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " mana in any combination of ").bind fun (add, colors) =>
    match (after? add "add ").bind positiveCount,
        ((colors.replace ", and/or " " ").replace ", " " ").splitOn " " |>.mapM addableSymbol? with
    | some k, some syms@(_ :: _ :: _) =>
      some (.addManaInAnyCombination (.controller .this) syms (Value.nat k), n)
    | _, _ => none

/-- `add {B} or {R}`: the player chooses one listed symbol. -/
def parseAddOneOfSentence (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (parseAddOneOf sentence).map fun actions =>
    (.playerSelectAction (.controller .this) (.range 1 1) actions, n)

/-- `<target> can't be blocked this turn`. The target is `n`. -/
def parseTargetCantBeBlockedThisTurn (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (before? (normSentence sentence) " can't be blocked this turn").bind fun who =>
    (parseTargetDesc who n).map fun sel =>
      (.continuous [.forbid (.block .any sel)] .endOfTurn, n + 1)

/-- `<this> deals damage equal to the number of Dwarves you control to each
opponent`. The source is this object. -/
def parseDealsDamageEqualCountToEachOpponent (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " deals damage equal to the number of ").bind
    fun (who, rest) =>
      if !damageSource? cardName who then none
      else
        (before? rest " to each opponent").bind (parseObjectDesc · false) |>.map fun among =>
          (.dealDamage .this (.opponent (.controller .this)) (.count among), n)

/-- `put a card from your hand on the bottom of your library`. -/
def parsePutHandCardOnBottom (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence "put a card from your hand on the bottom of your library" then
    some (.putOnBottomOfLibrary
      (.selected (.controller .this) (.range 1 1)
        (.intersection [.inHand, .owner (.controller .this)])), n)
  else none

/-- `draw cards equal to the greatest toughness among creatures you control`. -/
def parseDrawEqualGreatestToughness (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (after? (normSentence sentence) "draw cards equal to the greatest toughness among ").bind
    (parseObjectDesc · false) |>.map fun among =>
      (.draw (.controller .this) (.greatestToughness among), n)

/-- `put any number of creature cards from your hand onto the battlefield`. -/
def parsePutAnyFromHandOntoBattlefield (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (between? (normSentence sentence) "put any number of "
      " cards from your hand onto the battlefield").bind typesInPhrase |>.map fun ts =>
    (.putOntoBattlefield
      (.selected (.controller .this) .any
        (.intersection [.inHand, .owner (.controller .this), selectorOfTypes ts])), n)

/-- `it gets +X/+0 until end of turn, where X is the greatest power among
creatures you control`. -/
def parseGetsGreatestPowerUntilEnd (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " gets +x/+0 until end of turn, where x is the greatest power among ").bind
    fun (who, among) =>
      let subject := if who == "it" && n <= 1 then some (.source .this, n) else parseSubject cardName who n
      match subject, parseObjectDesc among false with
      | some (sel, n'), some amongSel =>
        some (.continuous [.addPower sel (.greatestPower amongSel)] .endOfTurn, n')
      | _, _ => none

/-- `each other Hero you control gets +X/+X until end of turn, where X is
<this>'s toughness`, or `another target creature you control gets +X/+0 …,
where X is <this>'s power`. X is this object's current value (CR 608.2h). -/
def parseGetsSelfStatUntilEnd (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  let s := normSentence sentence
  let split? (bonus : String) := (split2? s (" gets " ++ bonus ++ " until end of turn, where x is ")).map
    (bonus, ·)
  (split? "+x/+x" <|> split? "+x/+0").bind fun (bonus, who, stat) =>
    let v? : Option Value :=
      match before? stat "'s toughness", before? stat "'s power" with
      | some self, _ => if refersToSelf cardName self then some (.greatestToughness (.source .this)) else none
      | _, some self => if refersToSelf cardName self then some (.greatestPower (.source .this)) else none
      | _, _ => none
    let subject? : Option (Selector × Nat) :=
      match after? who "each " with
      | some rest => (parseObjectDesc rest false).map (·, n)
      | none => (parseTargetDesc who n).map (·, n + 1)
    match v?, subject? with
    | some v, some (sel, n') =>
      let again : Selector :=
        match sel with
        | .target k _ => .targetReference k
        | other => other
      let effects : List ContinuousEffect :=
        if bonus == "+x/+x" then [.addPower sel v, .addToughness again v] else [.addPower sel v]
      some (.continuous effects .endOfTurn, n')
    | _, _ => none

/-- `choose up to two creatures, then destroy the rest`. The chosen creatures
are variable `n` (not targeted, CR 608.2d). -/
def parseChooseUpToDestroyRest (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (between? (normSentence sentence) "choose up to " ", then destroy the rest").bind
    fun rest =>
      (split2? rest " ").bind fun (countText, noun) =>
        match positiveCount countText, typesInPhrase noun with
        | some k, some ts =>
          let kind := Selector.intersection [.permanent, selectorOfTypes ts]
          some (.sequence [
            .defineSelectorVariable n (.selected (.controller .this) (.range 0 (Value.nat k)) kind),
            .destroy (.intersection [.permanent, selectorOfTypes ts, .not (.variable n)])], n + 1)
        | _, _ => none

/-- `Double target creature's power and toughness until end of turn.` It gets
+X/+Y where X is its power and Y is its toughness (CR 701.10b). The creature
is target `n`. -/
def parseDoubleTargetPowerToughness (s : String) (n : Nat) : Option (CardAction × Nat) :=
  (between? s "double " "'s power and toughness until end of turn").bind parseTargetPhrase |>.map
    fun sel =>
      (.continuous [
        .addPower (.target n sel) (.greatestPower (.targetReference n)),
        .addToughness (.targetReference n) (.greatestToughness (.targetReference n))] .endOfTurn,
       n + 1)

/-- `Target creature you control fights target creature an opponent controls.`
The first creature is target `n`; the second is target `n + 1` (CR 701.12). -/
def parseTargetFightsTarget (s : String) (n : Nat) : Option (CardAction × Nat) :=
  (split2? s " fights ").bind fun (a, b) =>
    match parseTargetPhrase a, parseOppControlledTarget b with
    | some src, some dest => some (.fight (.target n src) (.target (n + 1) dest), n + 2)
    | _, _ => none

/-- `Target creature you control deals damage equal to twice its power to
target creature an opponent controls.` The source is target `n`. -/
def parseDealsTwicePower (s : String) (n : Nat) : Option (CardAction × Nat) :=
  (split2? s " deals damage equal to twice its power to ").bind fun (a, b) =>
    match parseTargetPhrase a, parseOppControlledTarget b with
    | some src, some dest =>
      some (.dealDamage (.target n src) (.target (n + 1) dest)
        (.product (.totalPower (.targetReference n)) (.int 2)), n + 2)
    | _, _ => none

/-- `you may put a land card from your hand onto the battlefield tapped`. -/
def parseMayPutFromHand (s : String) (n : Nat) : Option (CardAction × Nat) :=
  let (s, tapped) :=
    match before? s " tapped" with
    | some rest => (rest, true)
    | none => (s, false)
  (between? s "you may put " " card from your hand onto the battlefield").bind dropArticle? |>.bind
    typeOfOracle? |>.map fun t =>
      let card := Selector.selected (.controller .this) (.range 1 1)
        (.intersection [.inHand, .owner (.controller .this), .cardType t])
      (.optional (.controller .this)
        (if tapped then .putOntoBattlefieldInState card [.tapped] else .putOntoBattlefield card), n)

/-- `<this> deals damage equal to his power to any other target.` The target
is any target but this object (CR 115.4). -/
def parseSelfDealsPowerToAnyOther (cardName s : String) (n : Nat) : Option (CardAction × Nat) :=
  let ends := [" deals damage equal to his power to any other target",
    " deals damage equal to her power to any other target",
    " deals damage equal to its power to any other target"]
  (ends.findSome? (before? s ·)).bind fun who =>
    if refersToSelf cardName who then
      some (.dealDamageEqualToPower (.source .this) (.target n (.not .this)), n + 1)
    else none

/-- `<this> gains "<ability>" until end of turn.` The quoted text is an
activated ability of this object. -/
def parseGainsQuotedActivatedUntilEnd (cardName sentence : String) (n : Nat)
    (activated : String → Option Ability) : Option (CardAction × Nat) :=
  let s := copied sentence
  (before? s "\" until end of turn").bind (split2? · " gains \"") |>.bind fun (who, text) =>
    if !refersToSelf cardName who then none
    else (activated text).map fun a =>
      (.continuous [.gainAbility (.source .this) a] .endOfTurn, n)

/-- `Draw a card for each card you've discarded this turn.` -/
def parseDrawForEachDiscardedThisTurn (s : String) (n : Nat) : Option (CardAction × Nat) :=
  if s == "draw a card for each card you've discarded this turn" then
    some (.draw (.controller .this)
      (.count (.wasObjectSince (.discard (.controller .this)) .turnStart)), n)
  else none

/-- `Create X 1/1 green Squirrel creature tokens, where X is the number of
Squirrels you control.` -/
def parseCreateXTokensCount (s : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? s "create x ").bind (split2? · ", where x is the number of ") |>.bind
    fun (tokenText, among) =>
      match parseCreateCreatureTokens ("create two " ++ tokenText), parseObjectDesc among false with
      | some (.createTokens who (.nat 2) parts kws), some sel =>
        some (.createTokens who (.count sel) parts kws, n)
      | _, _ => none

/-- `you may draw <count>`, `you may mill <count>`, or
`you may create <creature tokens>`. The rest of the sentence is that action. -/
def parseYouMay (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "you may ").bind fun rest =>
    let counted (lead tail : String) (plural : Bool) : Option Nat :=
      (after? rest lead).bind fun afterLead =>
        (before? afterLead tail).bind fun countText =>
          if countText ++ tail == afterLead then nounCount? countText plural else none
    let draw :=
      (counted "draw " " card" false <|> counted "draw " " cards" true).map fun k =>
        .optional (.controller .this) (.draw (.controller .this) (Value.nat k))
    let mill :=
      (counted "mill " " card" false <|> counted "mill " " cards" true).map fun k =>
        .optional (.controller .this) (.mill (.controller .this) (Value.nat k))
    let create :=
      (parseCreateCreatureTokens rest).map fun action =>
        .optional (.controller .this) action
    (draw <|> mill <|> create).map (·, n)

/-- `Target player draws <count>.` The player is target `n`.
The sentence is that draw and nothing more. -/
def parseTargetPlayerDraws (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "target player draws ").bind fun rest =>
    let counted (tail : String) (plural : Bool) : Option Nat :=
      (before? rest tail).bind fun countText =>
        if countText ++ tail == rest then nounCount? countText plural else none
    (counted " card" false <|> counted " cards" true).map fun k =>
      (.draw (.target n .player) (Value.nat k), n + 1)

/-- Creating, drawing, and pumping sentences of a catalog effect. -/
private def parseCatalogSentenceCreate (cardName sentence s : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (parseCreateNamedCreatureTokens sentence).map (·, n) <|>
    parseYouMay sentence n <|>
    parseTargetPlayerDraws sentence n <|>
    parseDoubleTargetPowerToughness s n <|>
    parseGetsSelfStatUntilEnd cardName sentence n <|>
    parseDrawForEachDiscardedThisTurn s n <|>
    parseMayPutFromHand s n <|>
    parseSelfDealsPowerToAnyOther cardName s n <|>
    parseCreateXTokensCount s n <|>
    parseTargetFightsTarget s n <|>
    parseDealsTwicePower s n <|>
    parseTwoTargetPlayersEachDraw s n <|>
    parseCreateTokensForEach s n <|>
    parseLookTopPutLandsShuffle s n <|>
    parseAddManaForEach s n <|>
    parseAddManaInAnyCombination s n <|>
    parseTargetCantBeBlockedThisTurn s n <|>
    parseDealsDamageEqualCountToEachOpponent cardName s n <|>
    parsePutHandCardOnBottom s n <|>
    parseDrawEqualGreatestToughness s n <|>
    parsePutAnyFromHandOntoBattlefield s n <|>
    parseGetsGreatestPowerUntilEnd cardName s n <|>
    parseChooseUpToDestroyRest s n <|>
    parseDrawAndLoseLife s n <|>
    parseDiscardCards s n <|>
    parseCatalogAttach cardName s n <|>
    parseCantBeBlockedExceptBy s n <|>
    parseAddOneManaOfAnyColor s n <|>
    unchanged (parseReturnThisFromGraveyard s) n <|>
    parseTapOrUntap s n <|>
    parseSurveil s n <|>
    parseConnive cardName s n

/-- Damage, destroy, and mana sentences of a catalog effect. -/
private def parseCatalogSentenceResolve (cardName s : String) (n : Nat) :
    Option (CardAction × Nat) :=
  unchanged (parseCreateCreatureTokens s) n <|>
    unchanged (parseCreatePredefinedTokens s) n <|>
    parsePutCountersOn cardName s n <|>
    parseGetsGainsUntilEnd cardName s n <|>
    parseGainUntilEnd cardName s n <|>
    unchanged (parsePumpUntilEndOfTurn s) n <|>
    parseDealsDamageTo cardName s n <|>
    parseDealsGreatestManaValueDamage cardName s n <|>
    parseSelfDealsDamageEqualToPower cardName s n <|>
    parseDealsDividedDamage cardName s n <|>
    parseDestroyTarget s n <|>
    parseReturnToHand s n <|>
    parseTargetPlayerMills s n <|>
    parseLoseLife s n <|>
    parseEachPlayerSacrifices s n <|>
    parseSearchLibrary s n <|>
    parseSelfFights cardName s n <|>
    parseExileThenReturnTapped s n <|>
    parseExileThenReturn s n <|>
    parseWithoutKeywordCantBlock s n <|>
    parseDiscardUnlessArtifact s n <|>
    parseSpellsCostLessThisTurn s n <|>
    parseIfControlAnotherGainLife cardName s n <|>
    parseEachOpponentDiscards s n <|>
    parseDrawIfPowerAtLeast cardName s n <|>
    parseGainLifeForEach s n <|>
    parseTargetGainsThenSearchesBasic s n <|>
    parseOwnerPutsSecondOrBottom s n <|>
    parseAddMana s n <|>
    parseAddOneOfSentence s n <|>
    (parseAttachSelfToTarget cardName s n).bind fun (action, n') =>
      match action with
      | .attach _ (.target _ _) => some (action, n')
      | _ => none

/-- One sentence of a catalog effect. A leading `Then` is sequencing only.
`You create` is `create`. -/
@[noinline]
def parseCatalogSentenceOnce (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  let s := (after? (normSentence sentence) "then ").getD (normSentence sentence)
  let s := (after? s "you create ").map ("create " ++ ·) |>.getD s
  parseCatalogSentenceCreate cardName sentence s n <|>
    parseCatalogSentenceResolve cardName s n

/-- One sentence, or two clauses joined by `, then` or `and` when the whole
sentence is not one action. Existing sentence templates come first. -/
def parseCatalogSentence (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  let one (s : String) (n : Nat) :=
    parseSentence cardName s n <|> parseCatalogSentenceOnce cardName s n
  let pair (sep : String) : Option (CardAction × Nat) :=
    (split2? (normSentence sentence) sep).bind fun (a, b) =>
      (one a n).bind fun (first, n1) =>
        (one b n1).map fun (second, n2) => (.sequence [first, second], n2)
  let ifYouDont : Option (CardAction × Nat) :=
    let s := normSentence sentence
    let s := (after? s "then ").getD s
    (after? s "if you don't control ").bind (split2? · ", ") |>.bind fun (obj, effect) =>
      match youControlCondition? obj, one effect n with
      | some cond, some (action, n') => some (.if (.not cond) (flattenAction action), n')
      | _, _ => none
  one sentence n <|> ifYouDont <|> pair ", then " <|> pair " and "

/-- `sacrifice another creature or artifact`, `sacrifice another creature`,
`sacrifice an artifact`, or `sacrifice an artifact or discard a card`, as an
action the controller may take. The sacrificed permanent is one they control
(CR 701.17a). With `or`, the controller chooses which to do. -/
def parseMayAction (s : String) : Option CardAction :=
  let s := norm s
  let sacrifice (obj : String) : Option CardAction :=
    let (obj, other) :=
      match after? obj "another " with
      | some rest => (rest, true)
      | none => ((dropArticle? obj).getD obj, false)
    (typesInPhrase obj).map fun ts =>
      .sacrifice
        (.selected (.controller .this) (.range 1 1)
          (.intersection (
            (if other then [.not .this] else []) ++
            [.permanent, selectorOfTypes ts, youControl])))
  match split2? s " or discard " with
  | some (sac, discarded) =>
    match (after? sac "sacrifice ").bind sacrifice, parseCardCount discarded with
    | some sacAction, some k =>
      some (.playerSelectAction (.controller .this) (.range 1 1)
        [sacAction, .discard (.controller .this) (Value.nat k)])
    | _, _ => none
  | none => (after? s "sacrifice ").bind sacrifice

/-- `You may <action>. If you do, <effect>.` or `… When you do, <effect>.`
The optional action is action `n`. The effect happens only when that action
happened. -/
def parseMayIfYouDo (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [may, result] =>
    let r := normSentence result
    let effect? := after? r "if you do, " <|> after? r "when you do, "
    match (after? (normSentence may) "you may ").bind parseMayAction, effect? with
    | some action, some effect =>
      (parseCatalogSentence cardName effect n).map fun (then_, n') =>
        ([
          .optional (.controller .this) (.actionId n action),
          .if (.happened (.actionWithId n) .gameStart) (flattenAction then_)],
         n')
    | _, _ => none
  | _ => none

/-- `Exile the top card of your library. Until the end of your next turn, you
may play that card.` The exile is action `n`. -/
def parseExileTopUntilNextTurn (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [exile, play] =>
    if sentenceIs exile "exile the top card of your library" &&
        sentenceIs play "until the end of your next turn, you may play that card" then
      some (flattenAction (exileTopPlayUntilEndOfNextTurn n), n + 1)
    else none
  | _ => none

/-- `Add one mana of any color. Spend this mana only to cast an instant or
sorcery spell.` The mana is action `n`. Spending it on anything else is
forbidden. -/
def parseAddAnyColorSpendOnly (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [add, spend] =>
    if sentenceIs add "add one mana of any color" &&
        sentenceIs spend "spend this mana only to cast an instant or sorcery spell" then
      some ([.sequence [
        .actionId n (.addManaOfOneColor (.controller .this) ManaSymbol.anyColor 1),
        .continuous
          [.forbid (.spendManaCreatedByAction n (.not (.castSpell instantOrSorcery)))]
          .endOfTurn]], n)
    else none
  | _ => none

/-- `Choose target permanent card in your graveyard that was put there from
anywhere this turn. Return it to your hand.` The card is target `n`. -/
def parseChooseGraveyardCardReturn (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [choose, ret] =>
    if sentenceIs ret "return it to your hand" then
      (between? (normSentence choose) "choose target "
          " card in your graveyard that was put there from anywhere this turn").bind
        fun kind =>
          let kindSel? : Option Selector :=
            if kind == "permanent" then some .permanent else (typeOfOracle? kind).map Selector.cardType
          kindSel?.map fun kindSel =>
            ([.returnToHand (.target n (.intersection [
                .inGraveyard, kindSel, .owner (.controller .this),
                .wasObjectSince (.putToGraveyard .all) .turnStart]))], n + 1)
    else none
  | _ => none

/-- `Mill N cards. You may put a <kind> card from among the milled cards into
your hand.` Also `… from among those cards …`. The mill is action `n`. -/
def parseMillMayPut (ss : List String) (n : Nat) : Option (List CardAction × List String × Nat) :=
  match ss with
  | mill :: put :: rest =>
    let p := normSentence put
    let kind? :=
      (between? p "you may put " " card from among the milled cards into your hand") <|>
        (between? p "you may put " " card from among those cards into your hand")
    match (after? (normSentence mill) "mill ").bind parseCardCount,
        kind?.bind dropArticle? |>.bind typeOrSubtypeList? with
    | some k, some kind =>
      let among := extendIntersection [.wasObjectOfAction n] kind []
      some ([
        .actionId n (.mill (.controller .this) (Value.nat k)),
        .optional (.controller .this)
          (.returnToHand (.selected (.controller .this) (.range 1 1) among))],
        rest, n + 1)
    | _, _ => none
  | _ => none

/-- `Sacrifice an artifact or discard a nonland card`: one of those two costs. -/
def parseSacrificeOrDiscardCost (s : String) : Option Cost :=
  (after? (norm s) "sacrifice ").bind (split2? · " or discard ") |>.bind fun (obj, card) =>
    match (dropArticle? obj).bind typesInPhrase,
        (dropArticle? card).bind (before? · " card") with
    | some ts, some kind =>
      let discarded : Option Selector :=
        match after? kind "non" with
        | some t => (typeOfOracle? t).map fun t => .not (.cardType t)
        | none => (typeOfOracle? kind).map Selector.cardType
      discarded.map fun d => .or [.sacrificeCount (permanentWith ts [youControl]) 1, .discard d]
    | _, _ => none

/-- `You may pay {1}. When you do, <effect>.` The effect happens only if the
controller pays (CR 603.12). -/
def parseMayPayWhenYouDo (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [pay, result] =>
    let cost? : Option Cost :=
      ((after? (normSentence pay) "you may pay ").bind nonemptyMana? |>.map Cost.mana) <|>
        ((after? (normSentence pay) "you may ").bind parseSacrificeOrDiscardCost)
    match cost?, after? (normSentence result) "when you do, " with
    | some cost, some effect =>
      (parseCatalogSentence cardName effect n).map fun (action, n') =>
        ([.optionalPayFor (.controller .this) [cost] (flattenAction action)], n')
    | _, _ => none
  | _ => none

/-- `You may draw a card for each artifact you control. If you do, each
opponent draws a card.` Each of those objects is variable `n`. -/
def parseMayDrawForEachIfYouDo (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [may, result] =>
    match (after? (normSentence may) "you may draw a card for each ").bind (parseObjectDesc · false),
        normSentence result with
    | some among, "if you do, each opponent draws a card" =>
      some ([.optional (.controller .this) (.sequence [
        .forEachVariable n among [.draw (.controller .this) 1],
        .draw (.opponent (.controller .this)) 1])], n)
    | _, _ => none
  | _ => none

/-- `Put a +1/+1 counter on target creature. If that creature is another Hero,
put two +1/+1 counters on it instead.` The target is `n`. The extra counters
go on it when it is another permanent of that subtype. -/
def parsePutCounterMoreIfSubtype (ss : List String) (n : Nat) : Option (List CardAction × Nat) :=
  match ss with
  | [put, instead] =>
    match parsePutPlusOneOn? put, after? (normSentence instead) "if that creature is another " with
    | some (k, who), some rest =>
      (split2? rest ", ").bind fun (stText, more) =>
        match subtypeOfOracle? stText, (between? more "put " " instead").bind parsePutPlusOneOn?',
            parseTargetDesc who n with
        | some st, some (k', "it"), some sel =>
          if k' <= k then none
          else
            some ([
              .putCounter sel .plusOnePlusOne (.nat k),
              .if (.anySubtype (.intersection [.targetReference n, .not .this]) st)
                [.putCounter (.targetReference n) .plusOnePlusOne (.nat (k' - k))]],
              n + 1)
        | _, _, _ => none
    | _, _ => none
  | _ => none
where
  parsePutPlusOneOn?' (s : String) : Option (Nat × String) := parsePutPlusOneOn? ("put " ++ s)

/-- `Destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card.`
The creature is target `n`. Before it is destroyed, value variable `n`
records its power and selector variable `n + 1` its controller, so both are
its last-known information (CR 608.2h). With no target, that controller is
no player, so no one amasses and no card is drawn. -/
def parseDestroyAmassPowerDrawIfYours (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [destroy, amass, draw] =>
    let ctl := n + 1
    match (after? (normSentence destroy) "destroy ").bind (parseTargetDesc · n),
        (between? (normSentence amass)
          "its controller amasses " " x, where x is that creature's power").bind amassSubtype?,
        (after? (normSentence draw) "if you controlled that creature, ").bind parseDrawCards with
    | some sel, some st, some drawAction =>
      some ([
        .defineValueVariable n (.greatestPower sel),
        .defineSelectorVariable ctl (.controller (.targetReference n)),
        .destroy (.targetReference n),
        .keyword (.variable ctl) (.amass st (.variable n)),
        .if (.any (.intersection [.variable ctl, .controller .this])) [drawAction]],
        n + 2)
    | _, _, _ => none
  | _ => none

/-- `You may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, <this> deals X damage to each opponent.`
The discard is action `n`, and X is how many cards it discarded. Declining
discards nothing, so X is zero. The damage source is this card. -/
def parseMayDiscardHandDrawDamage (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [discard, draw, damage] =>
    let discarded := Value.count (.wasObjectOfAction n)
    if !sentenceIs discard "you may discard your hand" ||
        !sentenceIs draw "draw x cards, where x is the number of cards discarded this way" then
      none
    else
      (between? (normSentence damage)
          "if you have an enduring story, " " deals x damage to each opponent").bind fun who =>
        if !damageSource? cardName who then none
        else
          some ([
            .optional (.controller .this)
              (.actionId n (.discard (.controller .this) (.count cardsInYourHand))),
            .draw (.controller .this) discarded,
            .if controllerHasEnduringStory
              [.dealDamage (.source .this) (.opponent (.controller .this)) discarded]],
            n + 1)
  | _ => none

/-- Each sentence as one catalog action, in order. -/
def catalogSentenceActions (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  List.foldlM (fun (acc, n) s =>
    (parseCatalogSentence cardName s n).map fun (a, n') => (acc ++ [a], n'))
    ([], n) ss

/-- `<effect>. Then if you control four or more Treasures, sacrifice this Saga.
If you do, <effect>.` The count is of permanents of that subtype you control.
The sacrifice is action `n`; the last effect happens only if this was
sacrificed. -/
def parseThenIfControlSacrificeIfYouDo (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [first, thenIf, ifYouDo] =>
    (between? (normSentence thenIf) "then if you control " ", sacrifice this saga").bind
        (split2? · " or more ") |>.bind fun (countText, plural) =>
      match positiveCount countText, pluralCreatureType? plural,
          after? (normSentence ifYouDo) "if you do, " with
      | some k, some st, some effect =>
        (catalogSentenceActions cardName [first] (n + 1)).bind fun (firstActions, n1) =>
          (parseCatalogSentence cardName effect n1).map fun (last, n2) =>
            (firstActions ++ [
              .if (.greaterOrEqual
                  (.count (.intersection [.permanent, .subtype st, youControl])) (Value.nat k))
                [.actionId n (.sacrifice .this),
                 .if (.happened (.actionWithId n) .gameStart) (flattenAction last)]],
             n2)
      | _, _, _ => none
  | _ => none

/-- `You may pay {1}. If you do, <effect>.` The effect happens only if the
cost was paid (CR 118.1 / 608.2d). -/
def parseMayPayIfYouDo (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [pay, ifYouDo] =>
    match (after? (normSentence pay) "you may pay ").bind nonemptyMana?,
        after? (normSentence ifYouDo) "if you do, " with
    | some syms, some effect =>
      (parseCatalogSentence cardName effect n).map fun (action, n') =>
        ([.optionalPayFor (.controller .this) [.mana syms] (flattenAction action)], n')
    | _, _ => none
  | _ => none

/-- `You may tap any number of untapped Humans you control. Draw a card for
each Human tapped this way.` The tap is action `n`; any number includes none. -/
def parseTapAnyNumberDrawForEach (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [tap, draw] =>
    match (after? (normSentence tap) "you may tap any number of ").bind (parseObjectDesc · false),
        (between? (normSentence draw) "draw a card for each " " tapped this way") with
    | some sel, some _ =>
      some ([.actionId n (.tap (.selected (.controller .this) .any sel)),
        .draw (.controller .this) (.count (.wasObjectOfAction n))], n + 1)
    | _, _ => none
  | _ => none

/-- `Return target Elf card from your graveyard to your hand. You gain life
equal to that card's power.` That card is the target. -/
def parseReturnGyGainLifeEqualPower (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [ret, gain] =>
    if !sentenceIs gain "you gain life equal to that card's power" then none
    else
      (between? (normSentence ret) "return target " " from your graveyard to your hand").bind
        parseGraveyardCard |>.map fun sel =>
          ([.returnToHand (.target n sel),
            .gainLife (.controller .this) (.greatestPower (.targetReference n))], n + 1)
  | _ => none

/-- `Destroy all artifacts and enchantments your opponents control. You gain 1
life for each permanent destroyed this way.` The destruction is action `n`. -/
def parseDestroyAllGainLifePer (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [destroy, gain] =>
    if !sentenceIs gain "you gain 1 life for each permanent destroyed this way" then none
    else
      (after? (normSentence destroy) "destroy all ").bind
        (fun obj => parseObjectDesc (obj.replace " and " " or ") false) |>.map fun sel =>
          ([.actionId n (.destroy sel),
            .gainLife (.controller .this) (.count (.wasObjectOfAction n))], n + 1)
  | _ => none

/-- `Choose a creature type. Return all creatures that aren't of the chosen
type to their owners' hands.` The choice is action `n` (CR 205.3m). -/
def parseChooseTypeReturnOthers (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [choose, ret] =>
    if sentenceIs choose "choose a creature type" &&
        sentenceIs ret "return all creatures that aren't of the chosen type to their owners' hands" then
      some ([.actionId n (.chooseCreatureType (.controller .this)),
        .returnToHand (.intersection [
          .permanent, .cardType .creature, .not (.hasCreatureTypeChosenByAction n)])], n + 1)
    else none
  | _ => none

/-- `Add {R}{R}. Spend this mana only to cast Dwarf, Equipment, and Saga
spells.` The mana is action `n`; it can't be spent on anything else
(CR 106.6). -/
def parseAddManaSpendOnlySubtypes (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [add, spend] =>
    match (after? (normSentence add) "add ").bind nonemptyMana?,
        (between? (normSentence spend) "spend this mana only to cast " " spells").bind fun kinds =>
          (orList (kinds.replace ", and " ", ")).mapM subtypeOfOracle? with
    | some syms, some sts@(_ :: _) =>
      let spells := Selector.intersection [.spell, .union (sts.map Selector.subtype)]
      some ([.sequence [
        .actionId n (.addMana (.controller .this) syms),
        .continuous [.forbid (.spendManaCreatedByAction n (.not (.castSpell spells)))] .endOfTurn]],
        n + 1)
    | _, _ => none
  | _ => none

/-- `Add one mana of any color. Spend this mana only to cast a Hero spell or to
activate an ability of a Hero source.`, `… only to cast an artifact spell.`,
and `Add {U}. This mana can't be spent to cast a nonartifact spell.` The mana
is action `n`; the restricted spending is forbidden (CR 106.6). -/
def parseAddManaSpendRestricted (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [add, spend] =>
    let a := normSentence add
    let s := normSentence spend
    let add? : Option CardAction :=
      if a == "add one mana of any color" then
        some (.addManaOfOneColor (.controller .this) ManaSymbol.anyColor 1)
      else (after? a "add ").bind nonemptyMana? |>.map (.addMana (.controller .this) ·)
    let sourceSubtype? : Option Trigger :=
      (between? s "spend this mana only to cast a " " source").bind
          (split2? · " spell or to activate an ability of a ") |>.bind fun (k, k') =>
        if k != k' then none
        else (subtypeOfOracle? k).map fun st =>
          .not (.or (.castSpell (.intersection [.spell, .subtype st]))
            (.activateAbility (.subtype st)))
    let spellType? : Option Trigger :=
      (between? s "spend this mana only to cast an " " spell").bind typeOfOracle? |>.map fun t =>
        .not (.castSpell (.intersection [.spell, .cardType t]))
    let nonType? : Option Trigger :=
      (between? s "this mana can't be spent to cast a non" " spell").bind typeOfOracle? |>.map
        fun t => .castSpell (.intersection [.spell, .not (.cardType t)])
    match add?, sourceSubtype? <|> spellType? <|> nonType? with
    | some addAction, some forbidden =>
      some ([.sequence [
        .actionId n addAction,
        .continuous [.forbid (.spendManaCreatedByAction n forbidden)] .endOfTurn]], n + 1)
    | _, _ => none
  | _ => none

/-- `Look at the top three cards of your library. You may reveal a Hero card
from among them and put it into your hand. Put the rest on the bottom of your
library in any order.` The looked-at cards are action `n`; the revealed card is
action `n + 1`. The owner orders the rest (CR 401.4). -/
def parseLookAtTopRevealAnyOrder (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [look, reveal, rest] =>
    if normSentence rest != "put the rest on the bottom of your library in any order" then none
    else
      match (between? (normSentence look) "look at the top " " of your library").bind
          topCount?,
        (between? (normSentence reveal) "you may reveal "
          " card from among them and put it into your hand").bind dropArticle? |>.bind
          subtypeOfOracle? with
      | some k, some st =>
        some (lookAtTopMayRevealToHand n k (.subtype st) .putOnBottomOfLibrary, n + 2)
      | _, _ => none
  | _ => none

/-- `Choose a creature type. Create a Treasure token for each creature you
control of that type.` The choice is action `n` (CR 205.3m); each counted
creature is variable `n + 1`. -/
def parseChooseTypeCreateForEach (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [choose, create] =>
    if normSentence choose != "choose a creature type" then none
    else
      (before? (normSentence create) " for each creature you control of that type").bind
        createOneToken? |>.map fun token =>
          ([.actionId n (.chooseCreatureType (.controller .this)),
            .forEachVariable (n + 1)
              (.intersection [
                .permanent, .cardType .creature, youControl, .hasCreatureTypeChosenByAction n])
              [token]], n + 2)
  | _ => none

/-- `Destroy target land. Its controller may search their library for a basic
land card, put it onto the battlefield tapped, then shuffle.` The land is target
`n`; its controller searches (CR 701.19). -/
def parseDestroyThenControllerSearchesBasic (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [destroy, search] =>
    if normSentence search !=
        "its controller may search their library for a basic land card, put it onto the battlefield tapped, then shuffle"
    then none
    else
      match catalogSentenceActions cardName [destroy] n with
      | some ([.destroy (.target t sel)], n1) =>
        let who := Selector.controller (.targetReference t)
        some ([
          .destroy (.target t sel),
          .optional who (.searchLibraryThenShuffle who [
            .putOntoBattlefieldInState (.selected who (.range 1 1) basicLandInLibrary) [.tapped]])],
          n1)
      | _ => none
  | _ => none

/-- `Exile all creatures. Each player may put any number of creature cards from
their hand onto the battlefield. Then put all cards exiled this way into their
owners' hands. Exile <this>.` The exile is action `n`; each player is variable
`n + 1`. -/
def parseExileAllPutFromHandReturnExiled (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss.map normSentence with
  | [exileAll, put, ret, exileSelf] =>
    let kind? := (after? exileAll "exile all ").bind typesInPhrase
    let putKind? :=
      (between? put "each player may put any number of "
        " cards from their hand onto the battlefield").bind typeOfOracle?
    let self := (after? exileSelf "exile ").any (refersToSelf cardName)
    match kind?, putKind? with
    | some ts, some t =>
      if ret != "then put all cards exiled this way into their owners' hands" || !self then none
      else
        let p := Selector.variable (n + 1)
        some ([
          .actionId n (.exile (permanentWith ts [])),
          .forEachVariable (n + 1) .player [
            .optional p (.putOntoBattlefield
              (.selected p .any (.intersection [.inHand, .owner p, .cardType t])))],
          .returnToHand (.wasCreatedByAction n),
          .exile .this], n + 2)
    | _, _ => none
  | _ => none

/-- `<effect> if there are two or more creature cards in your graveyard.
Otherwise, <effect>.` The condition is checked on resolution. -/
def parseIfGraveyardOtherwise (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [first, other] =>
    (split2? first " if ").bind fun (effect, condText) =>
      (after? (normSentence other) "otherwise, ").bind fun otherText =>
        match graveyardCountCondition? (norm condText), catalogSentenceActions cardName [effect] n with
        | some cond, some (yes, n1) =>
          (catalogSentenceActions cardName [otherText] n1).map fun (no, n2) =>
            ([.ifElse cond yes no], n2)
        | _, _ => none
  | _ => none

/-- `You may put an artifact card from your hand onto the battlefield. If it's
an Equipment, attach it to <this>.` The put is action `n`. -/
def parseMayPutThenAttachEquipment (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [put, attach] =>
    match parseMayPutFromHand (normSentence put) n,
        (after? (normSentence attach) "if it's an equipment, attach it to ").map (refersToSelf cardName) with
    | some (.optional who (.putOntoBattlefield card), _), some true =>
      some ([.optional who (.sequence [
        .actionId n (.putOntoBattlefield card),
        .if (.anySubtype (.wasObjectOfAction n) .equipment)
          [.attach (.wasObjectOfAction n) (.source .this)]])], n + 1)
    | _, _ => none
  | _ => none

/-- Every sentence of `text` as catalog actions, in order. Multi-sentence
templates come first. A leading sentence may come before exiling the top card
to play later. -/
def catalogActionsFromText (cardName text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  let ss := sentences text
  parseMayIfYouDo cardName ss n <|>
    parseThenIfControlSacrificeIfYouDo cardName ss n <|>
    parseDestroyAmassPowerDrawIfYours ss n <|>
    parseMayDiscardHandDrawDamage cardName ss n <|>
    parseMayPayWhenYouDo cardName ss n <|>
    parseMayDrawForEachIfYouDo ss n <|>
    parseChooseGraveyardCardReturn ss n <|>
    parsePutCounterMoreIfSubtype ss n <|>
    ((parseMillMayPut ss n).bind fun (first, rest, n1) =>
      (catalogSentenceActions cardName rest n1).map fun (more, n2) => (first ++ more, n2)) <|>
    parseExileTopUntilNextTurn ss n <|>
    parseAddAnyColorSpendOnly ss n <|>
    parseChooseTypeCreateForEach ss n <|>
    parseMayPayIfYouDo cardName ss n <|>
    parseTapAnyNumberDrawForEach ss n <|>
    parseReturnGyGainLifeEqualPower ss n <|>
    parseDestroyAllGainLifePer ss n <|>
    parseChooseTypeReturnOthers ss n <|>
    parseAddManaSpendOnlySubtypes ss n <|>
    parseAddManaSpendRestricted ss n <|>
    parseLookAtTopRevealAnyOrder ss n <|>
    parseDestroyThenControllerSearchesBasic cardName ss n <|>
    parseIfGraveyardOtherwise cardName ss n <|>
    parseMayPutThenAttachEquipment cardName ss n <|>
    parseExileAllPutFromHandReturnExiled cardName ss n <|>
    (match ss with
      | first :: rest =>
        (catalogSentenceActions cardName [first] n).bind fun (a, n1) =>
          (parseExileTopUntilNextTurn rest n1).map fun (b, n2) => (a ++ b, n2)
      | [] => none) <|>
    catalogSentenceActions cardName ss n

/-- A card name with `. ` in it, such as `M.O.D.O.K.`, would split a
sentence. Such a name in `text` is this permanent. -/
def withoutDottedName (cardName text : String) : String :=
  if (cardName.splitOn ". ").length > 1 || cardName.endsWith "." then
    text.replace (cardName ++ " ") "this permanent "
  else text

/-- One effect of a triggered or activated ability. -/
def parseCatalogEffect (cardName text : String) (n : Nat) : Option (CardAction × Nat) :=
  (catalogActionsFromText cardName (withoutDottedName cardName text) n).bind
    fun (actions, n') => (combineActions actions).map (·, n')

/-- A spell you cast: `a noncreature spell`, `an instant or sorcery spell`,
`a Villain spell`, or `a spell`. -/
def parseSpellYouCast (s : String) : Option Selector :=
  let s := norm s
  if s == "an instant or sorcery spell" then some (.intersection [instantOrSorcery, youControl])
  else if s == "a spell" then some (.intersection [.spell, youControl])
  else
    (before? s " spell").bind dropArticle? |>.bind fun kind =>
      let kindSel :=
        ((after? kind "non").bind typeOfOracle? |>.map fun t => Selector.not (.cardType t)) <|>
          ((typeOfOracle? kind).map Selector.cardType) <|>
          ((subtypeOfOracle? kind).map Selector.subtype)
      kindSel.map fun k => .intersection [.spell, k, youControl]

/-- The event of a trigger condition (CR 603.1), after `when` or `whenever`:
this card entering, dying, attacking, or becoming blocked; another permanent
entering; creatures attacking together; one or more objects dealing damage
to a player; you sacrificing a token; a spell being cast; you drawing a
card; or a second draw or spell in a turn. -/
def parseTriggerEvent (cardName clause : String) : Option Trigger :=
  let c := norm clause
  let self (tail : String) : Option Unit :=
    (before? c tail).bind fun who => if refersToSelf cardName who then some () else none
  -- A plural name takes the plural verb (`The Sackville-Bagginses enter`).
  let selfEvent :=
    ((self " enters or attacks").map fun _ => Trigger.or (.enter .this) (.attack .this .all)) <|>
      ((self " enters" <|> self " enter").map fun _ => Trigger.enter .this) <|>
      ((self " dies" <|> self " die").map fun _ => Trigger.die .this) <|>
      ((self " attacks" <|> self " attack").map fun _ => Trigger.attack .this .all) <|>
      ((self " becomes blocked" <|> self " become blocked").map fun _ => Trigger.block .all .this) <|>
      ((self " deals combat damage to a player" <|> self " deal combat damage to a player").map fun _ =>
        Trigger.combatDamage .this .player)
  let fixed : Option Trigger :=
    match c with
    | "you attack" => some youAttack
    | "you draw a card" => some (.draw (.controller .this) .all)
    | "you draw your second card each turn" =>
      some (.ordinal 2 .turnStart (.draw (.controller .this) .all))
    | "a player casts their second spell each turn" =>
      some (.ordinal 2 .turnStart (.castSpell .spell))
    | "an opponent draws their second card each turn" =>
      some (.ordinal 2 .turnStart (.draw (.opponent (.controller .this)) .all))
    | "equipped creature attacks" => some (.attack (.hostOf .this) .all)
    | "equipped creature deals combat damage to a player" =>
      some (.combatDamage (.hostOf .this) .player)
    | "you sacrifice a token" =>
      some (.sacrifice (.intersection [.permanent, .token, youControl]))
    | _ => none
  let cast := (after? c "you cast ").bind parseSpellYouCast |>.map Trigger.castSpell
  let selfOrAnother :=
    (before? c " enters").bind (split2? · " or another ") |>.bind fun (who, other) =>
      if !refersToSelf cardName who then none
      else
        (parseObjectDesc ("another " ++ other) true).map fun sel =>
          Trigger.or (.enter .this) (.enter sel)
  let andOr :=
    (before? c " enters").bind (after? · "another ") |>.bind (split2? · " and/or ") |>.bind
      fun (a, b) =>
        let (b, ctl) := splitControllerClause b
        let ctlText := if ctl.isEmpty then "" else " you control"
        match parseObjectDesc ("another " ++ a ++ ctlText) false,
            parseObjectDesc ("another " ++ b ++ ctlText) false with
        | some x, some y => some (Trigger.enter (.union [x, y]))
        | _, _ => none
  let enters :=
    (before? c " enters").bind fun who =>
      let who := (dropArticle? who).getD who
      (parseObjectDesc who false).map Trigger.enter
  let returned :=
    (before? c " is returned to its owner's hand").bind fun who =>
      (parseObjectDesc who false).map Trigger.returnToHand
  let attackTogether :=
    (before? c " attack a player").bind fun who =>
      let counted :=
        ((after? who "one or more ").map (·, ([] : List SetPredicate))) <|>
          ((after? who "two or more ").map (·, [SetPredicate.countAtLeast 2]))
      counted.bind fun (obj, preds) =>
        (parseObjectDesc obj true).map fun sel => Trigger.attackSimultaneously sel .player preds
  let combat :=
    (before? c " deals combat damage to a player or battle").bind fun who =>
      (parseObjectDesc ((dropArticle? who).getD who) true).map fun sel =>
        Trigger.combatDamage sel (.union [.player, .cardType .battle])
  let damageTogether :=
    (before? c " deal damage to a player").bind fun who =>
      (after? who "one or more ").bind fun obj =>
        (parseObjectDesc obj true).map fun sel =>
          Trigger.damageSimultaneously sel .player []
  let leaves :=
    (before? c " leaves your graveyard").bind parseGraveyardCard' |>.map Trigger.leaveGraveyard
  let putCounters :=
    (after? c "you put one or more +1/+1 counters on ").bind fun obj =>
      let obj := (after? obj "one or more ").getD obj
      (parseObjectDesc obj false).map fun sel =>
        Trigger.putCountersSimultaneously (.controller .this) sel .plusOnePlusOne
  -- Plural `enter`, so one trigger for the group. Singular `enters` is per object.
  let enterTogether :=
    (before? c " enter").bind fun who =>
      (after? who "one or more ").bind fun obj =>
        (parseObjectDesc obj false).map fun sel =>
          Trigger.enterSimultaneously sel []
  selfEvent <|> fixed <|> cast <|> selfOrAnother <|> andOr <|> returned <|>
    attackTogether <|> combat <|> damageTogether <|> leaves <|> putCounters <|>
    enterTogether <|> enters
where
  parseGraveyardCard' (s : String) : Option Selector :=
    (dropArticle? s).bind parseGraveyardCard

/-- `When(ever) <event>, <effect>`. The first comma ends the trigger condition
(CR 603.1). -/
def splitTrigger? (line : String) : Option (String × String) :=
  let s := copied (rulesText line)
  let lower := norm s
  let lead :=
    if lower.startsWith "whenever " then some "whenever ".length
    else if lower.startsWith "when " then some "when ".length
    else none
  lead.bind fun k =>
    match (s.drop k).copy.splitOn ", " with
    | clause :: effect :: more =>
      some (copied clause, copied (String.intercalate ", " (effect :: more)))
    | _ => none

/-- A cast trigger whose spell targets something: `a spell that targets a
creature you control`, `an instant or sorcery spell that targets an artifact or
land`, or `a spell that targets one or more creatures`. The trigger is
trigger `n`; its spell is that trigger's first argument. -/
def parseCastTargetsTrigger (clause : String) (n : Nat) : Option (Trigger × Selector) :=
  (after? (norm clause) "you cast ").bind (split2? · " that targets ") |>.bind
    fun (spellText, targetText) =>
      let spell? :=
        if spellText == "an instant or sorcery spell" then
          some [Selector.spell, instantOrSorcery, youControl]
        else if spellText == "a spell" then some [Selector.spell, youControl]
        else none
      let target? :=
        match after? targetText "one or more " with
        | some obj => parseObjectDesc obj false
        | none => (dropArticle? targetText).bind (parseObjectDesc · false)
      match spell?, target? with
      | some spell, some target =>
        some (.triggerId n (.castSpell (.intersection (spell ++ [.hasTarget target]))), target)
      | _, _ => none

/-- `Copy that spell. You may choose new targets for the copy.` The spell is
the first argument of trigger `id` (CR 707.10). -/
def parseCopyThatSpell (id : Nat) (ss : List String) : Option (CardAction × List String) :=
  match ss with
  | copy :: choose :: rest =>
    if sentenceIs copy "copy that spell" &&
        sentenceIs choose "you may choose new targets for the copy" then
      some (.copyWithNewTargets (.controller .this) (.wasArgumentOfTrigger id 1), rest)
    else none
  | _ => none

/-- `Those creatures gain <keywords> until end of turn.` Those creatures are
the targets of the spell that is the first argument of trigger `id`. -/
def parseThoseCreaturesGain (id : Nat) (sentence : String) : Option CardAction :=
  (between? (normSentence sentence) "those creatures gain " " until end of turn").bind
    parseKeywordPhrase |>.bind fun kws =>
      gainUntilEnd
        (.intersection [.permanent, .cardType .creature, .isTargetOf (.wasArgumentOfTrigger id 1)])
        kws

/-- A cast trigger whose spell targets something, with its effect. -/
def parseCastTargetsLine (cardName line : String) (n : Nat) : Option (CardPart × Nat) :=
  (splitTrigger? line).bind fun (clause, effect) =>
    (parseCastTargetsTrigger clause n).bind fun (trigger, _) =>
      let ss := sentences effect
      let copied :=
        (parseCopyThatSpell n ss).bind fun (copy, rest) =>
          (catalogActionsFromText cardName (String.intercalate ". " rest) (n + 1)).bind
            fun (more, n') => (combineActions (copy :: more)).map (·, n')
      let those :=
        match ss with
        | [one] => (parseThoseCreaturesGain n one).map (·, n + 1)
        | _ => none
      (copied <|> those).map fun (action, n') => (.ability (.triggered trigger action), n')

/-- `Whenever you cast a spell that targets a creature you control, <effect>`
where the effect is about this card. The spell's targets are checked when the
ability resolves. -/
def parseCastTargetsYoursLine (cardName line : String) (n : Nat) : Option (CardPart × Nat) :=
  (splitTrigger? line).bind fun (clause, effect) =>
    (after? (norm clause) "you cast a spell that targets a ").bind fun obj =>
      (parseObjectDesc obj false).bind fun target =>
        (parseCatalogEffect cardName effect n).map fun (action, n') =>
          (.ability (.triggered (.castSpell (.intersection [.spell, youControl]))
            (.if (.targetsIncludeAny .this target) (flattenAction action))), n')

/-- `a` or `b`. `Condition` spells disjunction as the negation of both failing. -/
def either (a b : Condition) : Condition :=
  .not (.and (.not a) (.not b))

/-- `you attacked with a Hero this turn` or `an artifact entered the
battlefield under your control this turn`. -/
def thisTurnCondition? (s : String) : Option Condition :=
  let yours (obj : String) : Option Selector :=
    (dropArticle? obj).bind (parseObjectDesc · false) |>.map andYouControl
  ((between? s "you attacked with " " this turn").bind yours |>.map fun sel =>
    .happened (.attack sel .all) .turnStart) <|>
  ((before? s " entered the battlefield under your control this turn").bind yours |>.map fun sel =>
    .happened (.enter sel) .turnStart)

/-- The condition of an intervening `if` clause (CR 603.4). -/
def interveningCondition? (s : String) : Option Condition :=
  match norm s with
  | "you've drawn two or more cards this turn" =>
    some (.happened (.ordinal 2 .turnStart (.draw (.controller .this) .all)) .turnStart)
  | s =>
    thisTurnCondition? s <|>
      (split2? s " or ").bind fun (a, b) =>
        match thisTurnCondition? a, thisTurnCondition? b with
        | some ca, some cb => some (either ca cb)
        | _, _ => none

/-- `<effect>`, or `if <condition>, <effect>` when that condition is an
intervening if (CR 603.4). A condition this grammar does not know stays part
of the effect. The printed `if` is lowercase, as in the middle of a sentence. -/
def splitInterveningIf (effect : String) : Option Condition × String :=
  match (after? effect "if ").bind (split2? · ", ") with
  | some (c, rest) =>
    match interveningCondition? c with
    | some cond => (some cond, rest)
    | none => (none, effect)
  | none => (none, effect)

/-- Wrap `action` in an intervening if. No condition leaves the effect as printed. -/
def applyInterveningIf (cond? : Option Condition) (action : CardAction) : CardAction :=
  match cond? with
  | some c => CardAction.if c (flattenAction action)
  | none => action

/-- A triggered ability: `When(ever) <event>, <effect>`. -/
def parseCatalogTriggeredPlain (cardName line : String) (n : Nat) : Option (CardPart × Nat) :=
  let line := withoutDottedName cardName line
  parseCastTargetsLine cardName line n <|>
    parseCastTargetsYoursLine cardName line n <|>
    (splitTrigger? line).bind fun (clause, effect) =>
      (parseTriggerEvent cardName clause).bind fun trigger =>
        let (cond, effect) := splitInterveningIf effect
        (parseCatalogEffect cardName effect n).map fun (action, n') =>
          (.ability (.triggered trigger (applyInterveningIf cond action)), n')

/-- The triggered ability in quoted text, such as `Whenever Redwing attacks,
surveil 1.`, of an object named `name`. -/
def quotedTriggered? (name text : String) : Option Ability :=
  (parseCatalogTriggeredPlain name text 1).bind fun
    | (.ability a, _) => some a
    | _ => none

/-- `create Redwing, a legendary 1/1 blue Bird Scout creature token with flying
and "<ability>"`. The token has that name, supertype, power, toughness, color,
subtypes, keywords, and quoted triggered ability. -/
def parseCreateNamedToken (sentence : String) : Option CardAction :=
  let raw := copied sentence
  (if (norm raw).startsWith "create " then
      some ((raw.drop "create ".length).trimAscii.copy)
    else none).bind (split2? · ", a ") |>.bind fun (tokenName, rest) =>
    (split2? rest " creature token with ").bind fun (desc, abilities) =>
        (split2? abilities " and \"").bind fun (kwText, quotedRest) =>
        let kwText :=
          if kwText.endsWith "," then (kwText.dropEnd 1).trimAscii.copy else kwText
        let quotedText := (before? quotedRest "\"").getD quotedRest
        let words := desc.splitOn " " |>.map copied |>.filter (· != "")
        let (sups, words) :=
          match words with
          | w :: more =>
            match supertypeOfOracle? w with
            | some sup => ([sup], more)
            | none => ([], words)
          | [] => ([], [])
        match words with
        | pt :: colorText :: subtypeTexts =>
          match parseUnsignedPT pt, colorName? (norm colorText), subtypeTexts.mapM subtypeOfOracle?,
              parseKeywordPhrase kwText, quotedTriggered? tokenName quotedText with
          | some (p, t), some c, some (st :: sts), some kws, some quoted =>
            some (.createTokens (.controller .this) 1 (
              [.name tokenName, .type .creature] ++ sups.map CardPart.supertype ++
                (st :: sts).map CardPart.subtype ++
                [.colorIndicator [c], .power p, .toughness t] ++
                kws.map (fun k => .ability (.keyword k)) ++ [.ability quoted]))
          | _, _, _, _, _ => none
        | _ => none

/-- `Whenever an equipped creature you control attacks, it connives.` The
attacker is the host of an Equipment you control. -/
def parseEquippedAttacksConnives (line : String) : Option CardPart :=
  if normLine line == "whenever an equipped creature you control attacks, it connives" then
    let host := Selector.hostOf equipmentYouControl
    some (.ability (.triggered (.attack host .all) (.keyword host (.connive (.nat 1)))))
  else none

/-- `Whenever equipped creature attacks, create <tokens>. If that creature is
legendary, instead create <count> of those tokens that are tapped and
attacking.` That creature is this object's host. -/
def parseEquippedAttacksCreateInstead (line : String) : Option CardPart :=
  (splitTrigger? line).bind fun (clause, effect) =>
    if norm clause != "equipped creature attacks" then none
    else
      match sentences effect with
      | [create, instead] =>
        match parseCreateCreatureTokens create,
            between? (normSentence instead) "if that creature is legendary, instead create "
              " of those tokens that are tapped and attacking" with
        | some (.createTokens who k parts [.tapped]), some countText =>
          if (positiveCount countText).map Value.nat != some k then none
          else
            some (.ability (.triggered (.attack (.hostOf .this) .all)
              (.ifElse (.any (.intersection [.hostOf .this, .supertype .legendary]))
                [.createTokens who k parts [.tapped, .attacking]]
                [.createTokens who k parts [.tapped]])))
        | _, _ => none
      | _ => none

/-- `create a 1/1 green Minion creature token named Moloid with "<ability>"`.
The token has that name and the quoted triggered ability. -/
def parseCreateNamedQuotedToken (sentence : String) : Option CardAction :=
  (split2? (stripTrailingPeriod (copied sentence)) " named ").bind fun (head, rest) =>
    (split2? rest " with \"").bind fun (tokenName, quotedRest) =>
      let quotedText := (before? quotedRest "\"").getD quotedRest
      match parseCreateCreatureTokens head, quotedTriggered? tokenName quotedText with
      | some (.createTokens who k parts states), some quoted =>
        some (.createTokens who k (.name tokenName :: parts ++ [.ability quoted]) states)
      | _, _ => none

/-- A triggered ability, including one that creates a named token with a
quoted ability. -/
def parseCatalogTriggered (cardName line : String) (n : Nat) : Option (CardPart × Nat) :=
  (parseEquippedAttacksConnives line).map (·, n) <|>
    (parseEquippedAttacksCreateInstead line).map (·, n) <|>
    ((splitTrigger? line).bind fun (clause, effect) =>
      (parseTriggerEvent cardName clause).bind fun trigger =>
        ((parseCreateNamedToken effect <|> parseCreateNamedQuotedToken effect).map fun action =>
          (.ability (.triggered trigger action), n))) <|>
    parseCatalogTriggeredPlain cardName line n

/-- One printed activation cost, including `Discard this card`, `Pay N life`,
and `Sacrifice an artifact or discard a nonland card`. -/
def parseCatalogCost (cardName s : String) : Option Cost :=
  parseSacrificeOrDiscardCost s <|>
    parsePrintedCost cardName s <|>
    (parsePayLife s).map Cost.life <|>
    ((after? (norm s) "discard ").bind fun obj =>
      if refersToSelf cardName obj || obj == "this card" then some (.discard .this) else none)

/-- `Sacrifice Mount Doom and a legendary artifact`: this object and one other
matching permanent (CR 701.17a). -/
def parseSacrificeThisAnd (cardName s : String) : Option (List Cost) :=
  (after? (norm s) "sacrifice ").bind (split2? · " and ") |>.bind fun (self, obj) =>
    if !refersToSelf cardName self then none
    else
      (dropArticle? obj).bind (parseObjectDesc · false) |>.map fun sel =>
        [.sacrifice .this, .sacrificeCount sel 1]

/-- Costs separated by commas. One unrecognized cost fails the list.
Sacrificing a permanent that is not `another` or `this` is not a cost on its
own, only one item of a list. -/
def parseCatalogCosts (cardName s : String) : Option (List Cost) :=
  let parts := s.splitOn ", " |>.map copied |>.filter (· != "")
  let costs (part : String) : Option (List Cost) :=
    (parseSacrificeThisAnd cardName part) <|> (parseCatalogCost cardName part).map ([·])
  match parts with
  | [] => none
  | [one] => if (parseSacrificeAn one).isSome then none else costs one
  | _ => (parts.mapM costs).map List.flatten

/-- `Activate only if there are two or more creature cards in your graveyard.`
or `Activate only if you control a legendary creature.` -/
def parseActivateOnlyIf (s : String) : Option Condition :=
  ((after? (normSentence s) "activate only if you control ").bind youControlCondition?) <|>
  ((after? (normSentence s) "activate only if this land entered this turn or if you control ").bind
    youControlCondition? |>.map fun cond =>
      either (.happened (.enter (.source .this)) .turnStart) cond) <|>
  (after? (normSentence s) "activate only if ").bind graveyardCountCondition?

/-- `This ability costs {2} less to activate if you control a legendary
creature.` A static ability that reduces this ability's cost. -/
def parseAbilityCostsLessIf (s : String) : Option CardPart :=
  let controls :=
    (after? (normSentence s) "this ability costs ").bind
      (split2? · " less to activate if you control ") |>.bind fun (costText, obj) =>
        (nonemptyMana? costText).bind fun syms =>
          (youControlCondition? (copied obj)).map (syms, ·)
  let targets :=
    (after? (normSentence s) "this ability costs ").bind
      (split2? · " less to activate if it targets ") |>.bind fun (costText, obj) =>
        (nonemptyMana? costText).bind fun syms =>
          (dropArticle? obj).bind parseTargetObject |>.map fun sel =>
            (syms, Condition.targetsIncludeAny .this sel)
  (controls <|> targets).map fun (syms, cond) =>
    .ability (.static (.if cond [.reduceCost .this [.mana syms]]))

/-- `<costs>: <effect>`, with an optional activation limit (CR 602.5) or a
cost reduction that follows the effect. -/
def parseCatalogActivated (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  let line := withoutDottedName cardName line
  (splitPrintedAbility? line).bind fun (costText, effect) =>
    (parseCatalogCosts cardName costText).bind fun costs =>
      let ss := sentences effect
      let (body, limit) := splitActivateLimit ss
      let (body, extra, cond?) :=
        match body.reverse with
        | last :: restRev =>
          match parseActivateOnlyIf last, parseAbilityCostsLessIf last with
          | some cond, _ => (restRev.reverse, [], some cond)
          | none, some part => (restRev.reverse, [part], none)
          | none, none => (body, [], none)
        | [] => (body, [], none)
      if body.isEmpty then none
      else if body.map normSentence ==
          ["return this card from your graveyard to the battlefield tapped"] then
        let gyCond? :=
          match cond?, limit with
          | some cond, .unlimited => some cond
          | none, .asSorcery => some (.timeToCastSorcery (.controller .this))
          | _, _ => none
        gyCond?.map fun cond =>
          ([.ability (.graveyardActivatedIf cond costs
            (.putOntoBattlefieldInState (.intersection [.inGraveyard, .source .this])
              [.tapped]))] ++ extra, n)
      else
        let effect? :=
          (match body with
            | [one] => parseGainsQuotedUntilEnd cardName one n (quotedTriggered? cardName)
            | _ => none) <|>
          parseCatalogEffect cardName (String.intercalate ". " body) n
        effect?.map fun (action, n') =>
          match cond? with
          | some cond => ([.ability (.activatedIf cond costs action)] ++ extra, n')
          | none =>
            let (part, n'') := activatedWithCost n costs action limit n'
            ([part] ++ extra, n'')

/-- The permanent a static ability is about: the equipped or enchanted creature,
this card, or the printed object. A bare subtype is a creature when
`withCreature` is true. -/
def staticSubject? (cardName who : String) (withCreature : Bool) : Option Selector :=
  match who with
  | "equipped creature" | "enchanted creature" => some (.hostOf .this)
  | _ =>
    if refersToSelf cardName who then some .this else parseObjectDesc who withCreature

/-- `<objects> get +P/+T` or `<objects> get +P/+T for each <objects>`, with no
duration: a static ability (CR 604.2). `Equipped` and `enchanted` creature
is this object's host. A subtype is a creature of that subtype. -/
def parseCatalogStaticGets (cardName line : String) : Option (List CardPart) :=
  let s := normLine line
  if (split2? s " until end of turn").isSome then none
  else
    (splitGets? s).bind fun (who, rest) =>
      let who? := staticSubject? cardName who true
      let (ptText, has?) : String × Option (List Ability) :=
        match split2? rest " and has " <|> split2? rest " and have " with
        | some (pt, has) =>
          (pt, (parseKeywordPhrase has).map (List.map Ability.keyword) <|>
            (genericWard? has).map fun k => [Ability.keywordWithCost .ward [.mana [.generic k]]])
        | none => (rest, some [])
      match who?, has? with
      | some sel, some abilities =>
        match split2? ptText " for each " with
        | some (pt, each) =>
          match parsePowerToughness pt, parseObjectDesc each false with
          | some (p, t), some among =>
            let effects := scaledPowerToughness sel p t
              (fun k => if k == 1 then Value.count among else Value.timesCount k among)
              (fun k => if k == 1 then Value.count among else Value.timesCount k among)
            if effects.isEmpty then none
            else some (effects.map fun e => .ability (.static e))
          | _, _ => none
        | none =>
          (parsePowerToughness ptText).bind fun (p, t) =>
            (staticPowerToughness sel p t).map fun parts =>
              parts ++ abilities.map fun a => .ability (.static (.gainAbility sel a))
      | _, _ => none

/-- `<objects> have <keywords>` or `Equipped creature has <keywords>`: a static
ability. -/
def parseCatalogStaticHas (cardName line : String) : Option (List CardPart) :=
  let s := normLine line
  (split2? s " have " <|> split2? s " has ").bind fun (who, kwText) =>
    let who? := staticSubject? cardName who false
    match who?, parseKeywordPhrase kwText with
    | some sel, some kws =>
      if kws.isEmpty then none
      else some (kws.map fun k => .ability (.static (.gainAbility sel (.keyword k))))
    | _, _ => none

/-- `Other Elves you control have "{T}: Add {G} or {U}."`: the quoted
activated ability is granted by a static ability (CR 113.1a / 604.1). -/
def parseCatalogStaticHasQuoted (cardName line : String) : Option (List CardPart) :=
  (split2? (rulesText line) " have \"" <|> split2? (rulesText line) " has \"").bind
    fun (who, quoted) =>
      (before? quoted "\"").bind fun inner =>
        (parseObjectDesc who false).bind fun sel =>
          match parseCatalogActivated cardName inner 1 with
          | some ([.ability a], _) => some [.ability (.static (.gainAbility sel a))]
          | _ => none

/-- `<this> <mark> <object>`. The condition holds while this object's controller
does not control that object. `mark` is the printed restriction, such as
` enters tapped unless you control `. -/
def notYouControl? (cardName line mark : String) : Option Condition :=
  (split2? (normLine line) mark).bind fun (subject, obj) =>
    if !refersToSelf cardName subject then none
    else (youControlCondition? obj).map Condition.not

/-- `<this> enters tapped unless you control a legendary creature.` It enters
tapped while its controller controls no such permanent. The ability functions
in every zone (CR 113.6) so it can replace how this card enters the
battlefield. -/
def parseEntersTappedUnlessYouControl (cardName line : String) : Option CardPart :=
  (notYouControl? cardName line " enters tapped unless you control ").map fun cond =>
    .ability (.everywhereStatic (.if cond
      [.replace (.enter .this) [.putOntoBattlefieldInState .this [.tapped]]]))

/-- `<this> can't block unless you control a Goblin or Orc.` -/
def parseCantBlockUnlessYouControl (cardName line : String) : Option CardPart :=
  (notYouControl? cardName line " can't block unless you control ").map fun cond =>
    .ability (.static (.if cond [.forbid (.block .this .any)]))

/-- `As long as there are two or more creature cards in your graveyard,
<this> gets +P/+T [and is all creature types].` -/
def parseCatalogAsLongAsGraveyard (cardName line : String) : Option (List CardPart) :=
  (after? (normLine line) "as long as there are ").bind (split2? · " in your graveyard, ") |>.bind
    fun (countText, effect) =>
      (split2? countText " or more ").bind fun (k, cards) =>
        match positiveCount k, (before? cards " cards").bind typeOfOracle? with
        | some k, some t =>
          let cond := Condition.greaterOrEqual
            (.count (.intersection [.inGraveyard, .cardType t, .owner (.controller .this)]))
            (Value.nat k)
          let (effect, allTypes) :=
            match before? effect " and is all creature types" with
            | some e => (e, true)
            | none => (effect, false)
          (splitGets? effect).bind fun (who, ptText) =>
            if !refersToSelf cardName who then none
            else
              (parsePowerToughness ptText).bind fun (p, t) =>
                staticWhile cond
                  (flatPowerToughness .this p t ++
                    (if allTypes then [.gainAllSubtypes .this .creature] else [])) |>.map ([·])
        | _, _ => none

/-- `As long as you control another Elf, you may play an additional land on
each of your turns.` -/
def parseAnotherAdditionalLand (line : String) : Option CardPart :=
  (between? (normLine line) "as long as you control another "
      ", you may play an additional land on each of your turns").bind subtypeOfOracle? |>.map
    fun st =>
      .ability (.static (.if (.any (anotherSubtypeYouControl st))
        [.increaseLandPlayLimit (.controller .this) (Value.nat 1)]))

/-- `This spell costs {1} less to cast if you control a Villain`, or `… if it
targets an attacking creature`. The reduction functions on the stack
(CR 604.2). -/
def parseCatalogCostReduction (line : String) : Option CardPart :=
  (costsLessBy? (normLine line) " less to cast if ").bind fun (syms, cond) =>
    let controls :=
      (after? cond "you control ").bind dropArticle? |>.bind subtypeOfOracle? |>.map fun st =>
        Condition.anySubtype youControl st
    let targets :=
      (after? cond "it targets ").bind dropArticle? |>.bind parseTargetObject |>.map fun sel =>
        Condition.targetsIncludeAny .this sel
    (controls <|> targets <|> graveyardCountCondition? cond).map (reduceOnStack · syms)

/-- `As an additional cost to cast this spell, sacrifice an artifact or
creature.` The ability functions while this spell is on the stack. -/
def parseAdditionalCostSacrificeAn (line : String) : Option CardPart :=
  (after? (normLine line) "as an additional cost to cast this spell, ").bind parseSacrificeAn |>.map
    fun cost => .ability (.stackStatic (.additionalCost .this [cost]))

/-- `Equip Human {1}`: equip onto a creature of that subtype only. -/
def parseEquipSubtype (line : String) : Option CardPart :=
  (after? (rulesText line) "Equip ").bind fun rest =>
    let (word, costText) := splitNameCost rest
    match subtypeOfOracle? word, nonemptyMana? costText with
    | some st, some syms => some (.ability (.keywordWithSubtypeAndCost .equip st (.mana syms)))
    | _, _ => none

/-- `Creatures with flying can't attack you or block creatures you control.` -/
def parseKeywordCantAttackYouOrBlock (line : String) : Option CardPart :=
  (between? (normLine line) "creatures with " " can't attack you or block creatures you control").bind
    keywordOfOracle? |>.map fun k =>
      let with_ := Selector.intersection [.permanent, .cardType .creature, .keyword k]
      .ability (.static (.forbid (.or
        (.attack with_ (.controller .this))
        (.block with_ creaturesYouControl))))

/-- `<this card> can't be blocked` after an ability word. -/
def parseCatalogCantBeBlocked (cardName line : String) : Option CardPart :=
  (before? (normLine line) " can't be blocked").bind fun who =>
    if refersToSelf cardName who then some (.ability (.static (.forbid (.block .any .this))))
    else none

/-- A Saga chapter ability `I — <effect>` (CR 714.2). `III, IV — <effect>`
is one chapter ability for each number (CR 714.2b), numbered in turn. -/
def parseChapter (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  (match (rulesText line).splitOn " — " with
    | nums :: effect@(_ :: _) => some (copied nums, copied (" — ".intercalate effect))
    | _ => none).bind fun (nums, effect) =>
    ((nums.splitOn ", ").mapM chapterNumber?).bind fun ks =>
      if ks.isEmpty then none
      else
        ks.foldlM (fun (parts, n) k =>
          (((parseCreateNamedToken effect).map ([·], n)) <|>
              (catalogActionsFromText cardName effect n) <|>
              (parseSagaGainsQuoted cardName effect).map ([·], n)).map fun (actions, n') =>
            (parts ++ [CardPart.ability (.keywordWithEffect (.chapter k) actions)], n'))
          (([] : List CardPart), n)
where
  /-- `This Saga gains "<triggered ability>".` No duration is printed, so the
  ability lasts until the end of the game (CR 611.2a). -/
  parseSagaGainsQuoted (cardName effect : String) : Option CardAction :=
    (between? (copied effect) "This Saga gains \"" "\"").bind fun quoted =>
      if !(copied effect).endsWith "\"" then none else
      let quoted := (stripTrailingPeriod quoted)
      let quoted := (afterAbilityWord? quoted).getD quoted
      (quotedTriggered? cardName quoted).map fun ability =>
        .continuous [.gainAbility .this ability] .endOfGame

/-- A line about `equipped creature` or `enchanted creature`, which is an
ability of an Equipment or Aura rather than a spell. -/
def hostSubject? (line : String) : Bool :=
  (normLine line).startsWith "equipped creature " || (normLine line).startsWith "enchanted creature "

/-- `Whenever you discard a card, you may exile that card from your graveyard.
If you do, until the end of your next turn, you may play that card.` The
discard is trigger `n` and the exile is action `n`. -/
def parseDiscardMayExilePlay (line : String) (n : Nat) : Option (CardPart × Nat) :=
  if normLine line ==
      "whenever you discard a card, you may exile that card from your graveyard. if you do, until the end of your next turn, you may play that card" then
    some (.ability (.triggered (.triggerId n (.discard (.controller .this)))
      (.optional (.controller .this) (.sequence [
        .actionId n (.exile (.intersection [
          .inGraveyard, .wasArgumentOfTrigger n 1, .owner (.controller .this)])),
        .continuous [.canPlay (.controller .this) (.wasCreatedByAction n)]
          (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])]))), n + 1)
  else none

/-- `As long as you've put one or more +1/+1 counters on <this> this turn,
<this> has <keyword>.` -/
def parseKeywordIfCountersPutThisTurn (cardName line : String) : Option CardPart :=
  (after? (normLine line) "as long as you've put one or more +1/+1 counters on ").bind
    (split2? · " this turn, ") |>.bind fun (who, rest) =>
      (split2? rest " has ").bind fun (who', kw) =>
        if refersToSelf cardName who && damageSource? cardName who' then
          (keywordOfOracle? kw).map fun k =>
            .ability (.static (.if
              (.happened
                (.putCountersSimultaneously (.controller .this) .this .plusOnePlusOne)
                .turnStart)
              [.gainAbility .this (.keyword k)]))
        else none

/-- `If damage would be dealt to <this>, instead that damage is dealt, but all
other damage already dealt to him is healed.` A replacement effect (CR 614.1):
the damage is dealt after the damage already marked is removed. -/
def parseDamageHealsOther (cardName line : String) : Option CardPart :=
  (between? (normLine line) "if damage would be dealt to " " is healed").bind fun rest =>
    (split2? rest ", instead that damage is dealt, but all other damage already dealt to ").bind
      fun (who, pronoun) =>
        if refersToSelf cardName who && (pronoun == "him" || pronoun == "her" || pronoun == "it") then
          some (.ability (.static (.replace (.damage .all .this)
            [.healAllDamage .this, .keepReplacedAction])))
        else none

/-- `As this enchantment enters, choose a creature type.` then
`Creatures you control of the chosen type get +2/+2.` The choice is action
`n`. This object's controller makes it as a replacement of this object
entering (CR 614.12). The bonus is a static ability on creatures of that
type. A zero bonus is omitted. `+0/+0` is not an effect. -/
def parseAsEntersChooseCreatureType (cardName choose gets : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  (between? (normLine choose) "as " " enters, choose a creature type").bind fun who =>
    if !refersToSelf cardName who then none
    else
      (splitGets? (normLine gets)).bind fun (whoGets, ptText) =>
        match (before? whoGets " of the chosen type").bind parseControlledPhrase,
            parsePowerToughness ptText with
        | some (.intersection sel), some (p, t) =>
          let chosen := Selector.intersection (sel ++ [.hasCreatureTypeChosenByAction n])
          (staticPowerToughness chosen p t).map fun bonus =>
            (.ability (.static (.replace (.enter .this)
                [.actionId n (.chooseCreatureType (.controller .this)), .keepReplacedAction])) ::
              bonus,
              n + 1)
        | _, _ => none

/-- The step or phase of `At the beginning of <phase>` (CR 503.1 / 507.1 /
513.1): `combat on your turn`, `each combat`, `your upkeep`, `your end step`,
`each end step`, or `the upkeep of enchanted creature's controller`. -/
def beginningPhase? (s : String) : Option Trigger :=
  match norm s with
  | "combat on your turn" => some (.combatStart (.controller .this))
  | "each combat" => some (.combatStart .player)
  | "your upkeep" => some (.upkeep (.controller .this))
  | "your end step" => some (.endStep (.controller .this))
  | "each end step" => some (.endStep .player)
  | "the upkeep of enchanted creature's controller" =>
    some (.upkeep (.controller (.hostOf .this)))
  | _ => none

/-- `At the beginning of <phase>, [if <condition>,] <effect>.` The condition is
an intervening if (CR 603.4): checked when the phase begins and again on
resolution. -/
def parseBeginningOfTriggered (cardName line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (after? (copied (rulesText line)) "At the beginning of ").bind fun rest =>
    match rest.splitOn ", " with
    | phase :: more =>
      (beginningPhase? phase).bind fun trigger =>
        let (cond, effect) : Option Condition × String :=
          match more with
          | c :: effect@(_ :: _) =>
            match (after? (norm c) "if ").bind interveningCondition? with
            | some cond => (some cond, ", ".intercalate effect)
            | none => (none, ", ".intercalate more)
          | _ => (none, ", ".intercalate more)
        let thatPlayer : Option (CardAction × Nat) :=
          match trigger with
          | .upkeep who =>
            if norm effect == "that player draws a card" then some (.draw who 1, n) else none
          | _ => none
        (thatPlayer <|> parseCatalogEffect cardName effect n).map fun (action, n') =>
          (.ability (.triggered trigger (applyInterveningIf cond action)), n')
    | [] => none

/-- `∞ — At the beginning of <phase>, <effect>.` ∞ (CR 702.186) means this
permanent has that ability as long as it is harnessed. -/
def parseInfinity (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  (after? (rulesText line) "∞ — ").bind fun rest =>
    (parseBeginningOfTriggered cardName rest n).bind fun (part, n') =>
      match part with
      | .ability a => some ([.ability (.keywordWithAbility .infinity a)], n')
      | _ => none

/-- `The first creature spell you cast each turn costs {2} less to cast and can
be cast as though it had flash.` The spell is first when no creature spell of
yours was cast earlier this turn. Neither effect grants flash. -/
def parseFirstCreatureSpellCostsLessFlash (line : String) : Option (List CardPart) :=
  (between? (normLine line) "the first creature spell you cast each turn costs "
      " less to cast and can be cast as though it had flash").bind parseManaSymbols |>.map
    fun syms =>
      let creatureSpell := Selector.intersection [.spell, .cardType .creature, youControl]
      let first := Condition.didNotHappen (.castSpell creatureSpell) .turnStart
      [.ability (.static (.if first [.reduceCost creatureSpell [.mana syms]])),
       .ability (.static (.canBeCastAsThoughWithFlashIf creatureSpell first))]

/-- `Whenever another creature you control enters, if it has greater power or
toughness than <this>, put a +1/+1 counter on <this>.` The entering creature is
argument 1 of trigger 1. The comparison is an intervening if (CR 603.4). -/
def parseEntersGreaterThanSelfCounter (cardName line : String) : Option CardPart :=
  (splitTrigger? line).bind fun (clause, effect) =>
    (after? (norm clause) "another ").bind (before? · " enters") |>.bind fun obj =>
      (parseObjectDesc ("another " ++ obj) false).bind fun sel =>
        (after? (norm effect) "if it has greater power or toughness than ").bind
          (split2? · ", put a +1/+1 counter on ") |>.bind fun (a, b) =>
            if !(refersToSelf cardName a && refersToSelf cardName b) then none
            else
              let it := Selector.wasArgumentOfTrigger 1 1
              let greater := fun (v : Selector → Value) => Condition.greater (v it) (v (.source .this))
              some (.ability (.triggered (.triggerId 1 (.enter sel))
                (.if (either (greater .greatestPower) (greater .greatestToughness))
                  [.putCounter (.source .this) .plusOnePlusOne 1])))

/-- `Whenever you cast a spell that targets a creature you control, <this>
gains "<activated ability>" until end of turn.` -/
def parseCastTargetsYoursGainsQuoted (cardName line : String) (n : Nat) : Option (CardPart × Nat) :=
  (splitTrigger? line).bind fun (clause, effect) =>
    (after? (norm clause) "you cast a spell that targets a ").bind fun obj =>
      (parseObjectDesc obj false).bind fun target =>
        let quoted (text : String) : Option Ability :=
          match parseCatalogActivated cardName text 1 with
          | some ([.ability a], _) => some a
          | _ => none
        (parseGainsQuotedActivatedUntilEnd cardName effect n quoted).map fun (action, n') =>
          (.ability (.triggered (.castSpell (.intersection [.spell, youControl]))
            (.if (.targetsIncludeAny .this target) [action])), n')

/-- `Flying, first strike, ward {1}`: keywords, then generic ward last. -/
def parseKeywordsThenWard (line : String) : Option (List CardPart) :=
  let tokens := (rulesText line).splitOn "," |>.map copied |>.filter (· != "")
  match tokens.reverse with
  | last :: restRev@(_ :: _) =>
    match genericWard? last, restRev.reverse.mapM keywordOfOracle? with
    | some n, some kws =>
      some (kws.map (fun k => .ability (.keyword k)) ++
        [.ability (.keywordWithCost .ward [.mana [.generic n]])])
    | _, _ => none
  | _ => none

/-- `Prevent all damage that would be dealt to <this>.` A prevention effect
replaces that damage with nothing (CR 615.1). -/
def parsePreventAllDamageToSelf (cardName line : String) : Option CardPart :=
  (after? (normLine line) "prevent all damage that would be dealt to ").bind fun who =>
    if refersToSelf cardName who then
      some (.ability (.static (.replace (.damage .all .this) [])))
    else none

/-- `As long as an opponent has cast a spell this turn, you may cast spells as
though they had flash.` The spells don't gain flash (CR 702.8). -/
def parseFlashIfOpponentCast (line : String) : Option CardPart :=
  if normLine line ==
      "as long as an opponent has cast a spell this turn, you may cast spells as though they had flash" then
    some (.ability (.static (.canBeCastAsThoughWithFlashIf
      (.intersection [.spell, youControl])
      (.happened (.castSpell (.intersection [.spell, .controlled (.opponent (.controller .this))]))
        .turnStart))))
  else none

/-- One `you control <object>` piece: `an artifact creature` or `a Plan`. An
object of several card types has all of them. -/
def youControlPiece? (obj : String) : Option Condition :=
  youControlCondition? obj <|>
    ((dropArticle? obj).bind (fun o => ((norm o).splitOn " ").mapM typeOfOracle?) |>.map fun ts =>
      .any (.intersection ([.permanent] ++ ts.map Selector.cardType ++ [youControl])))

/-- `As long as you control an artifact creature or a Plan, <this> has
indestructible.` Either permanent satisfies the condition. -/
def parseAsLongAsYouControlHas (cardName line : String) : Option CardPart :=
  (after? (normLine line) "as long as you control ").bind (split2? · ", ") |>.bind
    fun (obj, rest) =>
      (split2? rest " has ").bind fun (who, kwText) =>
        if !refersToSelf cardName who then none
        else
          let cond? : Option Condition :=
            match split2? obj " or " with
            | some (a, b) =>
              match youControlPiece? a, youControlPiece? b with
              | some ca, some cb => some (either ca cb)
              | _, _ => none
            | none => youControlPiece? obj
          match cond?, parseKeywordPhrase kwText with
          | some cond, some kws =>
            some (.ability (.static (.if cond (kws.map fun k => .gainAbility .this (.keyword k)))))
          | _, _ => none

/-- `discard a card or pay {2}` as one cost with two choices. -/
def discardOrPayCost? (s : String) : Option Cost :=
  (split2? (norm s) " or pay ").bind fun (discard, pay) =>
    if discard != "discard a card" then none
    else (nonemptyMana? pay).map fun syms =>
      .or [.discard (.selected (.controller .this) (.range 1 1)
        (.intersection [.inHand, .owner (.controller .this)])), .mana syms]

/-- `As an additional cost to cast this spell, discard a card or pay {2}.` -/
def parseAdditionalCostDiscardOrPay (line : String) : Option CardPart :=
  (after? (normLine line) "as an additional cost to cast this spell, ").bind discardOrPayCost? |>.map
    fun cost => .ability (.stackStatic (.additionalCost .this [cost]))

/-- `Ward—Discard a card or pay {2}.` (CR 702.21) -/
def parseWardDiscardOrPay (line : String) : Option CardPart :=
  (after? (normLine line) "ward—").bind discardOrPayCost? |>.map fun cost =>
    .ability (.keywordWithCost .ward [cost])

/-- `You may play lands from your graveyard.` -/
def parseMayPlayLandsFromGraveyard (line : String) : Option CardPart :=
  if normLine line == "you may play lands from your graveyard" then
    some (.ability (.static (.canPlay (.controller .this)
      (.intersection [.inGraveyard, .cardType .land, .owner (.controller .this)]))))
  else none

/-- Static and cost lines of a catalog card, before its triggers. -/
private def parseCatalogLineStatic (cardName line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  (parseMayPlayLandsFromGraveyard line).map ([·], n) <|>
    (parseKeywordsThenWard line).map (·, n) <|>
    (parseEntersGreaterThanSelfCounter cardName line).map ([·], n) <|>
    (parseCastTargetsYoursGainsQuoted cardName line n).map (fun (p, n') => ([p], n')) <|>
    (parsePreventAllDamageToSelf cardName line).map ([·], n) <|>
    (parseFlashIfOpponentCast line).map ([·], n) <|>
    (parseAsLongAsYouControlHas cardName line).map ([·], n) <|>
    (parseAdditionalCostDiscardOrPay line).map ([·], n) <|>
    (parseWardDiscardOrPay line).map ([·], n) <|>
    (parseCreaturesWithPlusOneHave line).map (·, n) <|>
    (parseEquipSubtype line).map ([·], n) <|>
    (parseDiscardMayExilePlay line n).map (fun (p, n') => ([p], n')) <|>
    (parseKeywordIfCountersPutThisTurn cardName line).map ([·], n) <|>
    (parseDamageHealsOther cardName line).map ([·], n) <|>
    (parseCatalogCostReduction line).map ([·], n) <|>
    (parseAdditionalCostSacrificeAn line).map ([·], n) <|>
    (parseAnotherAdditionalLand line).map ([·], n) <|>
    (parseKeywordCantAttackYouOrBlock line).map ([·], n) <|>
    (parseCatalogCantBeBlocked cardName line).map ([·], n) <|>
    (parseCatalogAsLongAsGraveyard cardName line).map (·, n)

/-- Triggered, activated, and spell lines of a catalog card. -/
private def parseCatalogLineRest (cardName line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  parseChapter cardName line n <|>
    (parseCatalogTriggered cardName line n).map (fun (p, n') => ([p], n')) <|>
    parseCatalogActivated cardName line n <|>
    (parseCatalogStaticGets cardName line).map (·, n) <|>
    (parseCatalogStaticHasQuoted cardName line).map (·, n) <|>
    (parseEntersTappedUnlessYouControl cardName line).map ([·], n) <|>
    (parseCantBlockUnlessYouControl cardName line).map ([·], n) <|>
    (parseCatalogStaticHas cardName line).map (·, n) <|>
    (parseBeginningOfTriggered cardName line n).map (fun (p, n') => ([p], n')) <|>
    (parseFirstCreatureSpellCostsLessFlash line).map (·, n) <|>
    if hostSubject? line then none
    else
      spellActions ((catalogActionsFromText cardName line n).map fun (actions, n') =>
        (actions.flatMap flattenAction, n'))

/-- One catalog line that is not a mode list. -/
@[noinline]
def parseCatalogLine (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  parseCatalogLineStatic cardName line n <|> parseCatalogLineRest cardName line n

/-- A triggered ability whose effect is a `choose one —` list: the trigger
event, or `none` when `line` is not such a header. -/
def triggeredChooseOne? (cardName line : String) : Option Trigger :=
  (splitTrigger? line).bind fun (clause, effect) =>
    if norm effect == "choose one —" then parseTriggerEvent cardName clause else none

/-- One mode of a catalog modal ability. -/
def parseCatalogMode (cardName text : String) (n : Nat) : Option (CardAction × Nat) :=
  parseModeAction cardName text n <|> parseCatalogEffect cardName text n <|>
    (afterAbilityWord? text).bind fun rest =>
      parseModeAction cardName rest n <|> parseCatalogEffect cardName rest n

/-- `<this> can't be blocked if her/his/its/their power is N or less.` -/
def parseCantBeBlockedIfOwnPower (cardName line : String) : Option CardPart :=
  (split2? (normLine line) " can't be blocked if ").bind fun (subject, rest) =>
    if !refersToSelf cardName subject then none
    else
      let power? :=
        after? rest "her power is " <|> after? rest "his power is " <|>
          after? rest "its power is " <|> after? rest "their power is "
      (power?.bind (before? · " or less")).bind positiveCount |>.map fun p =>
        .ability (.static (.if
          (.lessOrEqual (.greatestPower (.source .this)) (.nat p))
          [.forbid (.block .any (.source .this))]))

/-- `Whenever you cast a creature spell, put X +1/+1 counters on target
creature you control, where X is that spell's mana value.` The spell is
trigger `n` and the creature is target `n`. -/
def parseCastCreaturePutCountersEqualMv (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (splitTrigger? line).bind fun (clause, effect) =>
    if norm clause != "you cast a creature spell" ||
        normSentence effect !=
          "put x +1/+1 counters on target creature you control, where x is that spell's mana value" then
      none
    else
      some (
        .ability (.triggered
          (.triggerId n (.castSpell (.intersection [.spell, .cardType .creature, youControl])))
          (.putCounter
            (.target n (.intersection [.permanent, .cardType .creature, youControl]))
            .plusOnePlusOne
            (.greatestManaValue (.wasArgumentOfTrigger n 1)))),
        n + 1)

/-- `Whenever this creature attacks, you may sacrifice another creature. If
you do, put a number of +1/+1 counters on this creature equal to the
sacrificed creature's power.` The sacrifice is action `n`. -/
def parseAttackMaySacrificePlusOneEqualPower (cardName line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onAttackN cardName line fun effect =>
    match (sentences effect).map normSentence with
    | [may, result] =>
      if may == "you may sacrifice another creature" &&
          result == "if you do, put a number of +1/+1 counters on this creature equal to the sacrificed creature's power" then
        some (
          .sequence [
            .optional (.controller .this)
              (.actionId n
                (.sacrifice
                  (.selected (.controller .this) (.range 1 1)
                    (.intersection [.not .this, .permanent, .cardType .creature, youControl])))),
            .if (.happened (.actionWithId n) .gameStart)
              [.putCounter (.source .this) .plusOnePlusOne
                (.greatestPower (.wasObjectOfAction n))]],
          n + 1)
      else none
    | _ => none

/-- `When <this> enters, put a hone counter on <this> for each creature target
opponent controls. Attach <this> to up to one target creature you control.`
The opponent is target `n`. The creature is target `n + 1`. -/
def parseEnterHonePerOppAttach (cardName line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences (rulesText line) with
  | [entered, attach] =>
    let attachWho :=
      (after? (normSentence attach) "attach ").bind
        (before? · " to up to one target creature you control")
    onEnterN cardName entered fun effect =>
      (after? (norm effect) "put a hone counter on ").bind
        (before? · " for each creature target opponent controls") |>.bind fun who =>
          match attachWho with
          | some whom =>
            if refersToSelf cardName who && refersToSelf cardName whom then
              some (
                .sequence [
                  .putCounter (.source .this) (.hone)
                    (.count
                      (.intersection [
                        .permanent,
                        .cardType .creature,
                        .controlled (.target n (.opponent (.controller .this)))])),
                  .attach .this
                    (.targets (n + 1) (.range 0 1)
                      (.intersection [.permanent, .cardType .creature, youControl]))],
                n + 2)
            else none
          | none => none
  | _ => none

/-- `<this> enters with a hope counter on it for each creature you control`,
or `<this> enters with X +1/+1 counters on it`. Both replace how this enters. -/
def parseEntersWithCounters (cardName line : String) : Option CardPart :=
  let s := normLine line
  let hope :=
    (before? s " enters with a hope counter on it for each creature you control").bind
      fun who =>
        if !refersToSelf cardName who then none
        else
          some (.ability (.static (.replace (.enter .this) [
            .putCounter (.source .this) (.hope)
              (.count
                (.intersection [
                  .permanent,
                  .cardType .creature,
                  youControl])),
            .keepReplacedAction])))
  let plus :=
    (before? s " enters with x +1/+1 counters on it").bind fun who =>
      if !refersToSelf cardName who then none
      else
        some (.ability (.static (.replace (.enter .this) [
          .putCounter (.source .this) .plusOnePlusOne .x,
          .keepReplacedAction])))
  hope <|> plus

/-- `At the beginning of your end step, remove a hope counter from this
enchantment. If you do, draw a card. Then if this enchantment has no hope
counters on it, sacrifice it and you gain 4 life.` The removal is action `n`. -/
def parseEndStepRemoveHopeDrawSac (line : String) (n : Nat) : Option (CardPart × Nat) :=
  match (sentences (rulesText line)).map normSentence with
  | [remove, draw, thenSac] =>
    if remove == "at the beginning of your end step, remove a hope counter from this enchantment" &&
        draw == "if you do, draw a card" &&
        thenSac == "then if this enchantment has no hope counters on it, sacrifice it and you gain 4 life" then
      some (
        .ability (.triggered (.endStep (.controller .this)) (.sequence [
          .actionId n (.removeCounter (.source .this) (.hope) (.nat 1)),
          .if (.happened (.actionWithId n) .gameStart) [
            .draw (.controller .this) (.nat 1),
            .if (.not (.any (.intersection [.source .this, .hasCounter (.hope)]))) [
              .sacrifice (.source .this),
              .gainLife (.controller .this) (.nat 4)]]])),
        n + 1)
    else none
  | _ => none

/-- Keyword, counter, and activated-ability lines. Tried before triggers. -/
private def parseOneLineHead (cardName : String) (line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  (keywordParts? line).map (·, n) <|>
    sole (parseCantBeBlockedIfOwnPower cardName line) n <|>
    sole (parseEntersWithCounters cardName line) n <|>
    carry (parseCastCreaturePutCountersEqualMv line n) <|>
    carry (parseAttackMaySacrificePlusOneEqualPower cardName line n) <|>
    carry (parseEnterHonePerOppAttach cardName line n) <|>
    carry (parseEndStepRemoveHopeDrawSac line n) <|>
    sole (parseEntersTapped cardName line) n <|>
    sole (parseEntersTappedUnlessEquipment cardName line) n <|>
    sole (parseTypecycling line) n <|>
    sole (parseHarness cardName line) n <|>
    parseInfinity cardName line n <|>
    carry (parseActivatedAbility cardName line n) <|>
    parseActivatedCreateCostsLess cardName line n <|>
    carry (parseActivatedDiscardDraw cardName line n) <|>
    carry (parseActivatedAddOrLoot cardName line n) <|>
    sole (parseTapAddOneOf line) n <|>
    carry (parseTapAddAnyColorEqualToPower cardName line n) <|>
    sole (parseAnotherElfEntersGets line) n <|>
    carry (parseLandYouControlEnters line n) <|>
    sole (parseLandfallCreate line) n <|>
    (parseLandsCharacteristic cardName line).map (·, n) <|>
    (parseCreaturesPowerCharacteristic cardName line).map (·, n) <|>
    (parseCardsInHandPowerCharacteristic cardName line).map (·, n) <|>
    sole (parseCantBeCountered line) n <|>
    sole (parseCastAsThoughFlash line) n <|>
    (parseStaticGets line).map (·, n) <|>
    (parseOtherSubtypeYouControlGets line).map (·, n) <|>
    sole (parseCreaturesWithPlusOneHaveMenace line) n <|>
    sole (parseYouCastNoncreatureAmass line) n <|>
    sole (parseYouCastNoncreaturePumpAndDamage cardName line) n <|>
    sole (parseYouCastSpellIfTreasureDrawLoseLife line) n

/-- Attack, enters, and other triggered lines. -/
private def parseOneLineMiddle (cardName : String) (line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  sole (parseYouAttackAmass line) n <|>
    sole (parseYouAttackRecruit line) n <|>
    sole (parseEnterOrAttackRecruit cardName line) n <|>
    sole (parseEnterAmass cardName line) n <|>
    sole (parseDiesAmass cardName line) n <|>
    sole (parseEnterSearchForest cardName line) n <|>
    carry (parseEnterSearchBasicToHand cardName line n) <|>
    carry (parseEnterDealDamageDestroyIfSubtype cardName line n) <|>
    sole (parseGraveyardReturn line) n <|>
    carry (parseOwnerShuffleDraw cardName line n) <|>
    carry (parseReturnFromGyAttach line n) <|>
    carry (parseEnterExileOppGyLoseLife cardName line n) <|>
    sole (parseEquipAbilitiesTargetingThisCostLess line) n <|>
    sole (parseCostReduction line) n <|>
    sole (parseCostLessByFlyingPower line) n <|>
    sole (parseInstantSorceryCostLessByEquippedPower line) n <|>
    sole (parseHasteIfAnother cardName line) n <|>
    sole (parseLifelinkIfAnother cardName line) n <|>
    sole (parseFirstEquipFreeIfEnduringStory line) n <|>
    sole (parseEnduringStoryGets cardName line) n <|>
    sole (parseEnduringStoryTeamGets line) n <|>
    sole (parseEnduringStoryTeamWard line) n <|>
    sole (parseEnduringStoryAttackTax line) n <|>
    sole (parseDoesntUntapUnlessEnduringStory cardName line) n <|>
    sole (parseThisOrNontokenSubtypeEntersCreate cardName line) n <|>
    sole (parseOpponentFirstNoncreatureRecruit line) n <|>
    sole (parseAttackTriggered line) n <|>
    carry (parseAttackTargetGains cardName line n) <|>
    carry (parseAttackDamageEqualTreasures cardName line n) <|>
    carry (parseAttackSetBasePT cardName line n) <|>
    sole (parseFerociousThisAttacks line) n <|>
    sole (parseFerociousYouAttack line) n <|>
    sole (parseFerociousBeginCombat line) n

/-- Enters, static, equipment, and spell lines, then the catalog grammar. -/
private def parseOneLineTail (cardName : String) (line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  carry (parseEnterGainLifeMaySearchBasicOnTop cardName line n) <|>
    sole (parseEnterYouGainLife cardName line) n <|>
    sole (parseThresholdGets cardName line) n <|>
    carry (parseEnterUntapPlusOneIfSubtype cardName line n) <|>
    sole (parseEnterRecruit cardName line) n <|>
    sole (parseDiesRecruit cardName line) n <|>
    sole (parseEnterScry cardName line) n <|>
    sole (parseEnterCreateTreasure cardName line) n <|>
    sole (parseEnterCreateNamedEquipment cardName line) n <|>
    sole (parseEnterCreateTappedTreasuresEqualOppArtifacts cardName line) n <|>
    carry (parseEnterLookAtTopReveal cardName line n) <|>
    carry (parseEnterExileTopMayPlay cardName line n) <|>
    carry (parseEnterPutPlusOneOnTarget cardName line n) <|>
    carry (parseEnterReturnOtherPlusOne cardName line n) <|>
    sole (parseEnterDraw cardName line) n <|>
    sole (parseEnterEachOpponentDiscards cardName line) n <|>
    carry (parseEnterDividedDamage cardName line n) <|>
    carry (parseEnterMayDiscardDraw cardName line n) <|>
    carry (parseEnterTargetOpponentSacrifices cardName line n) <|>
    carry (parseDiesOppGets cardName line n) <|>
    carry (parseOtherCreaturesDieScry line n) <|>
    sole (parseDrawSecondPlusOne line) n <|>
    sole (parseYouDrawPlusOne line) n <|>
    sole (parseCantBeBlockedByTokens cardName line) n <|>
    sole (parseCantBeBlockedByPower cardName line) n <|>
    sole (parseCantBeBlocked cardName line) n <|>
    sole (parseCantBlock cardName line) n <|>
    sole (parseBecomesTargetDraw cardName line) n <|>
    sole (parseFirstMainAddMana line) n <|>
    sole (parseCantAttackUnlessNOther cardName line) n <|>
    sole (parseAnotherSubtypeOrEquipmentEntersDraw line) n <|>
    sole (parseArtifactYouControlEntersDraw line) n <|>
    sole (parseUpkeepCreateCreature line) n <|>
    sole (parseYourEndStepDraw line) n <|>
    carry (parseEnterCreateThenAttach cardName line n) <|>
    carry (parseEnterAmassThenAttach cardName line n) <|>
    carry (parseEnterAttachToTarget cardName line n) <|>
    carry (parseEnterAttachTargetEquipment cardName line n) <|>
    sole (parseFlashback line) n <|>
    sole (parseKicker line) n <|>
    sole (parseSneak line) n <|>
    sole (parseAffinity line) n <|>
    sole (parseWard line) n <|>
    sole (parseCrew line) n <|>
    sole (parseTeamwork line) n <|>
    sole (parseGift line) n <|>
    sole (parseCombatDamageLoot cardName line) n <|>
    sole (parseAdditionalCostSacrificeCreature line) n <|>
    sole (parseAdditionalCostSacrificeOrPay line) n <|>
    carry (parseEnchant line n) <|>
    (parseEquippedHasAndCantBeBlocked line).map (·, n) <|>
    (parseEquippedGets line).map (·, n) <|>
    sole (parseEquipPayLife line) n <|>
    sole (parseEquip line) n <|>
    spellActions (actionsFromText cardName line n) <|>
    parseCatalogLine cardName line n <|>
    (afterAbilityWord? line).bind (parseCatalogLine cardName · n)

/-- One non-empty Oracle line. A reminder-only line contributes no parts.
Anything else that the grammar does not cover fails.
The first parser that accepts the line wins. -/
@[noinline]
def parseOneLine (cardName : String) (line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  if (rulesText line).isEmpty then some ([], n)
  else
    parseOneLineHead cardName line n <|>
      parseOneLineMiddle cardName line n <|>
      parseOneLineTail cardName line n

/-- `Landfall — Whenever a land you control enters, choose one —`.
`Landfall` may be omitted. The em dash after `choose one` keeps this from
being only an ability-word line. -/
def landfallChooseOne? (line : String) : Bool :=
  let choose := landYouControlEnters ++ "choose one —"
  match after? (normLine line) "landfall — " with
  | some rest => rest == choose
  | none => normLine line == choose

/-- How a list of `•` modes after a header becomes card parts, and how one
mode is read. -/
structure ModeList where
  wrap : List CardAction → List CardPart
  mode : String → Nat → Option (CardAction × Nat)

/-- `<trigger>, choose up to X —`. The controller chooses up to X distinct modes.
`X` is the value of X (CR 107.3). -/
def chooseUpToXModes (cardName : String) (trigger : Trigger) : ModeList where
  wrap modes :=
    [.ability (.triggered trigger (.chooseUniqueModes (.range (.nat 0) .x) modes))]
  mode := parseCatalogMode cardName

/-- A triggered “choose one —” ability: exactly one mode (CR 700.2). -/
def triggeredModes (cardName : String) (trigger : Trigger) : ModeList where
  wrap modes := [.ability (.triggered trigger (.chooseUniqueModes (.range 1 1) modes))]
  mode := parseCatalogMode cardName

/-- `<trigger>, choose one that hasn't been chosen this turn —`. Mode `i` may be
chosen only if no player chose it this turn. -/
def restrictedModes (cardName : String) (trigger : Trigger) : ModeList where
  wrap modes :=
    [.ability (.triggered trigger (.chooseModeRestricted (.controller .this)
      ((List.range modes.length).zip modes |>.map fun (i, action) =>
        (i + 1, .didNotHappen (.modeWithIdChosen .player (i + 1)) .turnStart, [action]))))]
  mode := parseCatalogMode cardName

/-- `Choose up to two. Return those cards from your graveyard to your hand.`
Each mode is `Target <type> card.`, a card in your graveyard. -/
def chooseUpToReturnModes (k : Nat) : ModeList where
  wrap modes :=
    [.actions [.playerSelectAction (.controller .this) (.range 0 (Value.nat k))
      (modes.map fun sel => sel)]]
  mode text n :=
    (between? (normSentence text) "target " " card").bind typeOfOracle? |>.map fun t =>
      (.returnToHand (.target n (.intersection [.inGraveyard, .cardType t, .owner (.controller .this)])),
        n + 1)

/-- A header whose `•` modes follow: a triggered `choose one —`, a triggered
`choose one that hasn't been chosen this turn —` (after an ability word), a
triggered `choose up to X —`, or
`Choose up to N. Return those cards from your graveyard to your hand.` -/
def modeListHeader? (cardName line : String) : Option ModeList :=
  let line' := (afterAbilityWord? line).getD line
  let restricted :=
    (splitTrigger? line').bind fun (clause, effect) =>
      if norm effect == "choose one that hasn't been chosen this turn —" then
        (parseTriggerEvent cardName clause).map (restrictedModes cardName)
      else if norm effect == "choose up to x —" then
        (parseTriggerEvent cardName clause).map (chooseUpToXModes cardName)
      else none
  let returnCards :=
    (between? (normLine line) "choose up to " ". return those cards from your graveyard to your hand").bind
      positiveCount |>.map chooseUpToReturnModes
  ((triggeredChooseOne? cardName line).map (triggeredModes cardName)) <|> restricted <|> returnCards

/-- `Power-up — <cost>: <effect>` (CR 702.193). The ability is number `n'`,
the next number after its effect. It may be activated only if it has not
been activated since the game began. While this permanent entered this
turn, the ability costs `manaCost`, this card's mana cost, less. `.this` in
that reduction is the ability, so the permanent is its source. A card with
no mana cost is not recognized. -/
def parsePowerUp (cardName : String) (manaCost : List ManaSymbol) (line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  if manaCost.isEmpty then none
  else
    (after? (rulesText line) "Power-up — ").bind fun rest =>
      (parseOneLine cardName rest n).bind fun
        | ([.ability (.activated costs action)], n') =>
          some ([.ability (.abilityId n' (.activatedWithStaticIf
            (.didNotHappen (.abilityWithIdActivated n') .gameStart) costs action
            (.if (.happened (.enter (.source .this)) .turnStart)
              [.reduceCost .this [.mana manaCost]])))], n' + 1)
        | _ => none

/-- One line outside a mode list. -/
def parseLine (cardName : String) (manaCost : List ManaSymbol) (line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  parsePowerUp cardName manaCost line n <|> parseOneLine cardName line n

mutual
/-- Lines outside a `Choose one —` list. `parseModeLines` reads the list. -/
def parseBodyLines (cardName : String) (manaCost : List ManaSymbol) :
    List String → Nat → Option (List CardPart × Nat)
  | [], n => some ([], n)
  | line :: rest, n =>
    if landfallChooseOne? line then
      parseListedModes cardName manaCost (triggeredModes cardName (.enter landsYouControl))
        rest n []
    else
      match modeListHeader? cardName line with
      | some list => parseListedModes cardName manaCost list rest n []
      | none =>
      match chooseHeader? line with
      | some orBoth => parseModeLines cardName manaCost rest n [] orBoth
      | none =>
        let oneLine (more : Nat → Option (List CardPart × Nat)) :=
          (parseLine cardName manaCost line n).bind fun (here, nHere) =>
            (more nHere).map fun (more, nMore) => (here ++ more, nMore)
        match rest with
        | [] => oneLine (parseBodyLines cardName manaCost [])
        | gets :: after =>
          ((parseAsEntersChooseCreatureType cardName line gets n).bind fun (here, nHere) =>
            (parseBodyLines cardName manaCost after nHere).map fun (more, nMore) =>
              (here ++ more, nMore)) <|>
            oneLine (parseBodyLines cardName manaCost (gets :: after))

/-- Bullet modes after a header such as a landfall “choose one —” line.
A bullet that does not parse fails. No bullets fails rather than dropping
the printed choice. A later non-bullet ends the list. -/
def parseListedModes (cardName : String) (manaCost : List ManaSymbol) (list : ModeList)
    (lines : List String) (n : Nat) (acc : List CardAction) : Option (List CardPart × Nat) :=
  let modesPart := list.wrap
  match lines with
  | [] =>
    match acc with
    | [] => none
    | modes => some (modesPart modes, n)
  | line :: rest =>
    match stripModeBullet line with
    | some text =>
      (list.mode text n).bind fun (action, n') =>
        parseListedModes cardName manaCost list rest n' (acc ++ [action])
    | none =>
      match acc with
      | [] => none
      | modes =>
        (parseLine cardName manaCost line n).bind fun (here, nHere) =>
          (parseBodyLines cardName manaCost rest nHere).map fun (more, nMore) =>
            (modesPart modes ++ here ++ more, nMore)

/-- `•` modes after `Choose one —` or `Choose one or both —`.
A later non-mode line ends the list.
No parsed modes fails rather than dropping the printed choice. -/
def parseModeLines (cardName : String) (manaCost : List ManaSymbol) (lines : List String)
    (n : Nat) (acc : List CardAction) (orBoth : Bool) : Option (List CardPart × Nat) :=
  match lines with
  | [] => (chooseOneParts acc orBoth).map fun parts => (parts, n)
  | line :: rest =>
    match stripModeBullet line with
    | some text =>
      (parseCatalogMode cardName text n).bind fun (action, n') =>
        parseModeLines cardName manaCost rest n' (acc ++ [action]) orBoth
    | none =>
      (chooseOneParts acc orBoth).bind fun head =>
        match chooseHeader? line with
        | some nested =>
          (parseModeLines cardName manaCost rest n [] nested).map fun (more, nMore) =>
            (head ++ more, nMore)
        | none =>
          (parseLine cardName manaCost line n).bind fun (here, nHere) =>
            (parseBodyLines cardName manaCost rest nHere).map fun (more, nMore) =>
              (head ++ here ++ more, nMore)
end

/-- Oracle lines, including `Choose one —` lists. `manaCost` is this card's
mana cost. -/
def parseMainLines (cardName : String) (manaCost : List ManaSymbol) (lines : List String)
    (n : Nat) : Option (List CardPart × Nat) :=
  parseBodyLines cardName manaCost lines n

def nameOfParts (parts : List CardPart) : Option String :=
  parts.findSome? fun
    | .name n => some n
    | _ => none

/-- Leading `sacrifice a creature` additional-cost lines, and the lines left. -/
def peelLeadingSacrificeCreatureCosts (lines : List String) :
    List CardPart × List String :=
  match lines with
  | [] => ([], [])
  | line :: rest =>
    match parseAdditionalCostSacrificeCreature line with
    | some part =>
      let (more, left) := peelLeadingSacrificeCreatureCosts rest
      (part :: more, left)
    | none => ([], lines)

/-- A Gatherer Adventure face: `Name {cost}`, a type line, then rules text.
A missing name or cost, a line that is not a type line, or effect text the
grammar does not cover makes the parse fail. No effect lines is a face
with no spell effect. A leading sacrifice-a-creature additional cost is an
ability of the face. `Draw a card` is that face's effect only after such a
cost; a draw with no other text stays unrecognized. A lone sentence that
creates creature tokens is also an effect. -/
def parseAdventure (cardName : String) (lines : List String) (n : Nat) :
    Option (List CardPart) :=
  match lines with
  | [] => none
  | nameLine :: rest =>
    (parseNameAndCost nameLine).bind fun nameParts =>
      match rest with
      | [] => some nameParts
      | typeLine :: effectLines =>
        (parseTypeLine typeLine).bind fun typeParts =>
          -- An Adventure face refers to itself by its own name.
          let faceName := nameOfParts nameParts |>.getD cardName
          match effectLines with
          | [] => some (nameParts ++ typeParts)
          | _ =>
            let (costParts, restLines) := peelLeadingSacrificeCreatureCosts effectLines
            let text := String.intercalate " " restLines
            let tokens :=
              match sentences text with
              | [one] => (parseCreateCreatureTokens one).map fun action => ([action], n)
              | _ => none
            let actions? : Option (List CardAction) :=
              if restLines.isEmpty then some []
              else
                match actionsFromText faceName text n <|> tokens with
                | some (actions, _) =>
                  if actions.isEmpty then none else some actions
                | none =>
                  if costParts.isEmpty then none
                  else (parseDrawCards (rulesText text)).map fun action => [action]
            actions?.map fun actions =>
              let actionParts :=
                if actions.isEmpty then [] else [.actions actions]
              nameParts ++ typeParts ++ costParts ++ actionParts

/-- Successive spell lines are one effect, in printed order. -/
def mergeConsecutiveActions (parts : List CardPart) : List CardPart :=
  go parts []
where
  go : List CardPart → List CardPart → List CardPart
    | [], acc => acc.reverse
    | .actions here :: rest, .actions earlier :: acc =>
      go rest
        (.actions (earlier.flatMap flattenAction ++ here.flatMap flattenAction) :: acc)
    | part :: rest, acc => go rest (part :: acc)

end OracleParts

open OracleParts

/-- Parse printed Oracle text into `CardPart`s.
The patterns this accepts are the module's recognized Oracle text.
`name` is the card being parsed. Text that uses that name, the short name
before a comma (CR 201.5), or that name's first word when it is not an
article, means this card, as do `this` and `this <type>`.
`Gollum the Abandoned` refers to itself as `Gollum`.
Returns `none` when a line, sentence, mode, or Adventure face is not
recognized. Reminder parentheticals are not rules text. Empty text is
`some []`. Successive spell lines are one effect, in printed order.
`manaCost` is the card's printed mana cost. Only abilities that refer to
that cost, such as power-up, read it. -/
def parseOracleParts (name : String) (text : String) (manaCost : List ManaSymbol := []) :
    Option (List CardPart) :=
  let lines :=
    text.splitOn "\n" |>.map (·.trimAscii.copy) |>.filter (· != "")
  let (main, adv) := splitAdventure lines
  (parseMainLines name manaCost main 1).bind fun (mainParts, n) =>
    let mainParts := mergeConsecutiveActions mainParts
    match adv with
    | [] => some mainParts
    | _ =>
      (parseAdventure name adv n).map fun alt =>
        mainParts ++ [.alternative alt]

#guard parseOracleParts (name := "") "Lifelink" == some [.ability (.keyword .lifelink)]
#guard parseOracleParts (name := "") "Flying, deathtouch" ==
  some [.ability (.keyword .flying), .ability (.keyword .deathtouch)]
#guard parseOracleParts (name := "")
  "Reach (This creature can block creatures with flying.)" ==
  some [.ability (.keyword .reach)]
#guard parseOracleParts (name := "") "Whenever this creature attacks, draw a card." ==
  some [.ability
     (.triggered
       (.attack .this .all)
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "") "When another creature enters, draw a card." ==
  some [.ability
     (.triggered
       (.enter
         (.intersection
           [.not .this,
            .permanent,
            .cardType .creature]))
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "") "When Bilbo Baggins enters, draw a card." == none
#guard parseOracleParts (name := "Gandalf") "When Bilbo Baggins enters, draw a card." == none
#guard parseOracleParts (name := "Bilbo") "When Bilbo Baggins enters, draw a card." == none
#guard parseOracleParts (name := "Bilbo Baggins, Burglar")
    "When Bilbo Baggins enters, draw a card." ==
  some [.ability (.triggered (.enter .this) (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "Bilbo Baggins, Burglar")
    "When Bilbo Baggins, Burglar enters, draw a card." ==
  some [.ability (.triggered (.enter .this) (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "") "When this creature enters, draw two cards." ==
  some [.ability (.triggered (.enter .this) (.draw (.controller .this) 2))]
#guard parseOracleParts (name := "")
  "Whenever you draw your second card each turn, draw a card." ==
  some [.ability
     (.triggered
       (.ordinal
         2
         .turnStart
         (.draw (.controller .this) .all))
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "")
  "Whenever you draw your second card each turn, put a +1/+1 counter on target creature." ==
  some [.ability
     (.triggered
       (.ordinal
         2
         .turnStart
         (.draw (.controller .this) .all))
       (.putCounter
         (.target
           1
           (.intersection
             [.permanent, .cardType .creature]))
         .plusOnePlusOne
         1))]
#guard parseOracleParts (name := "Lakeshore Apothecary")
  "Whenever you draw your second card each turn, put a +1/+1 counter on this creature." ==
  some [.ability (
    .triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      (.putCounter (.source .this) .plusOnePlusOne 1))]
#guard parseOracleParts (name := "")
  "Whenever you draw a card, draw a card." ==
  some [.ability (
    .triggered (.draw (.controller .this) .all) (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "")
  "Whenever you draw a card, put a +1/+1 counter on target creature." ==
  some [.ability (
    .triggered (.draw (.controller .this) .all)
      (.putCounter (.target 1 (.intersection [.permanent, .cardType .creature])) .plusOnePlusOne 1))]
#guard parseOracleParts (name := "")
  "Whenever you draw a card, if you control another Hero, put a +1/+1 counter on this creature." == none
#guard parseOracleParts (name := "Ravenhill Flock")
  "Whenever you draw a card, put a +1/+1 counter on this creature." ==
  some [.ability (
    .triggered
      (.draw (.controller .this) .all)
      (.putCounter (.source .this) .plusOnePlusOne 1))]
#guard parseOracleParts (name := "Ravenhill Flock")
  "Flying\nWhenever you draw a card, put a +1/+1 counter on this creature." ==
  some [
    .ability (.keyword .flying),
    .ability (
      .triggered
        (.draw (.controller .this) .all)
        (.putCounter (.source .this) .plusOnePlusOne 1))]
#guard parseOracleParts (name := "Brave Brawler") (manaCost := [.generic 1, .mono .white])
  "Power-up — {4}{W}: Put two +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)" ==
  some [.ability (
    .abilityId 1
      (.activatedWithStaticIf
        (.didNotHappen (.abilityWithIdActivated 1) .gameStart)
        [.mana [.generic 4, .mono .white]]
        (.putCounter (.source .this) .plusOnePlusOne 2)
        (.if (.happened (.enter (.source .this)) .turnStart)
          [.reduceCost .this [.mana [.generic 1, .mono .white]]])))]
#guard parseOracleParts (name := "Brave Brawler")
  "Power-up — {4}{W}: Put two +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)" ==
  none
#guard parseOracleParts (name := "Hercules, Prince of Power") (manaCost := [.generic 2, .mono .green])
  "Power-up — {4}{G}: Put a +1/+1 counter on Hercules. He gains vigilance, indestructible, and haste until end of turn. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)" ==
  some [.ability (
    .abilityId 1
      (.activatedWithStaticIf
        (.didNotHappen (.abilityWithIdActivated 1) .gameStart)
        [.mana [.generic 4, .mono .green]]
        (.sequence [
          .putCounter (.source .this) .plusOnePlusOne 1,
          .continuous [
            .gainAbility (.source .this) (.keyword .vigilance),
            .gainAbility (.source .this) (.keyword .indestructible),
            .gainAbility (.source .this) (.keyword .haste)]
            .endOfTurn])
        (.if (.happened (.enter (.source .this)) .turnStart)
          [.reduceCost .this [.mana [.generic 2, .mono .green]]])))]
#guard parseOracleParts (name := "Human Torch, Johnny Storm")
  "Whenever you draw a card, if you control another Hero, Human Torch deals 1 damage to target opponent." ==
  some [.ability (
    .triggered (.draw (.controller .this) .all)
      (.if (.any (.intersection [.not .this, .permanent, .subtype .hero, .controlled (.controller .this)]))
        [.dealDamage .this (.target 1 (.opponent (.controller .this))) (.nat 1)]))]
#guard parseOracleParts (name := "Viv Vision, Teen Synthezoid")
  "Cybernetic Senses — Whenever Viv Vision attacks, draw a card if her power is 4 or greater." ==
  some [.ability (
    .triggered (.attack .this .all)
      (.if (.any (.intersection [.source .this, .powerAtLeast (.int 4)]))
        [.draw (.controller .this) (.nat 1)]))]
#guard parseOracleParts (name := "")
  "{6}: Each opponent discards a card. Create a 2/2 colorless Robot Villain artifact creature token." ==
  some [.ability (
    .activated [.mana [.generic 6]]
      (.sequence [
        .discard (.opponent (.controller .this)) (.nat 1),
        .createTokens (.controller .this) (.nat 1)
          [.type .artifact, .type .creature, .subtype .robot, .subtype .villain,
            .colorIndicator [], .power 2, .toughness 2]
          []]))]
#guard parseOracleParts (name := "") "Scry 2." ==
  some [.actions [.scry (.controller .this) 2]]
#guard parseOracleParts (name := "")
  "Scry 2. (Then exile this card. You may cast the creature later from exile.)" ==
  some [.actions [.scry (.controller .this) 2]]
#guard parseOracleParts (name := "")
  "Target creature you control gains hexproof until end of turn." ==
  some [.actions [
    .continuous
      [.gainAbility
        (.target 1 (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)]))
        (.keyword .hexproof)]
      .endOfTurn]]
#guard parseOracleParts (name := "")
  "{3}{W}: Creatures you control get +1/+1 until end of turn." ==
  some [.ability (
    .activated
      [.mana [.generic 3, .mono .white]]
      (.continuous
        [.addPower
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]) (Value.int 1),
         .addToughness
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]) (Value.int 1)]
        .endOfTurn))]
#guard parseOracleParts (name := "") "Tap one or two target creatures." ==
  some [.actions [
    .tap (.targets 1 (.range 1 2) (.intersection [.permanent, .cardType .creature]))]]
#guard parseOracleParts (name := "") "Tap two or one target creatures." == none
#guard parseOracleParts (name := "") "Tap 0 target creatures." == none
#guard parseOracleParts (name := "") "Tap 0 or 1 target creatures." == none
#guard parseOracleParts (name := "") "//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure" ==
  some [.alternative [
    .name "Spew Flame",
    .manaCost [.generic 4, .mono .red],
    .type .sorcery,
    .subtype .adventure]]
#guard parseOracleParts (name := "")
  "This spell costs {3} less to cast if it targets a tapped creature." ==
  some [.ability (
    .stackStatic
      (.if
        (.targetsIncludeAny
          .this
          (.intersection [
            .permanent,
            .cardType .creature,
            .tapped]))
        [.reduceCost .this [.mana [.generic 3]]]))]
#guard parseOracleParts (name := "")
  "This spell costs {1} less to cast if it targets an attacking nontoken creature." ==
  some [.ability (
    .stackStatic
      (.if
        (.targetsIncludeAny
          .this
          (.intersection [
            .permanent,
            .cardType .creature,
            .attacking .all,
            .not .token]))
        [.reduceCost .this [.mana [.generic 1]]]))]
#guard parseOracleParts (name := "")
  "This spell costs {1} less to cast if it targets an attacking creature." ==
  some [.ability
     (.stackStatic
       (.if
         (.targetsIncludeAny
           .this
           (.intersection
             [.permanent,
              .cardType .creature,
              .attacking .all]))
         [.reduceCost
            .this
            [.mana [.generic 1]]]))]
#guard parseOracleParts (name := "") "Magnificent End deals 5 damage to target creature." == none
#guard parseOracleParts (name := "Shock") "Magnificent End deals 5 damage to target creature." == none
#guard parseOracleParts (name := "Magnificent End")
    "Magnificent End deals 5 damage to target creature." ==
  some [.actions [
    .dealDamage
      .this
      (.target 1 (.intersection [.permanent, .cardType .creature]))
      (.nat 5)]]
#guard parseOracleParts (name := "") "This spell deals 5 damage to target creature." ==
  some [.actions [
    .dealDamage
      .this
      (.target 1 (.intersection [.permanent, .cardType .creature]))
      (.nat 5)]]
#guard parseOracleParts (name := "") "This spell deals 0 damage to target creature." == none
#guard parseOracleParts (name := "Smaug, the Great Calamity")
    "//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure\nSpew Flame deals 5 damage to target creature." ==
  some [.alternative [
    .name "Spew Flame",
    .manaCost [.generic 4, .mono .red],
    .type .sorcery,
    .subtype .adventure,
    .actions [
      .dealDamage
        .this
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        (.nat 5)]]]
#guard
  let others : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled (.controller .this)]
  parseOracleParts (name := "")
    "Flying\nWhenever this creature attacks, it gets +1/+1 until end of turn for each other creature you control." ==
  some [
    .ability (.keyword .flying),
    .ability (
      .triggered
        (.attack .this .all)
        (.continuous
          [.addPower (.source .this) (Value.count others),
           .addToughness (.source .this) (Value.count others)]
          .endOfTurn))]
#guard parseOracleParts (name := "") "Untap target creature you control." ==
  some [.actions [
    .untap
      (.target
        1
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)]))]]
#guard parseOracleParts (name := "")
  "Untap target creature you control. It gets +2/+2 until end of turn. If it's a Dwarf, you may attach an Equipment you control to it." ==
  some [.actions [
    .untap
      (.target
        1
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])),
    .continuous [.addPower (.targetReference 1) (Value.int 2),
                 .addToughness (.targetReference 1) (Value.int 2)] .endOfTurn,
    .if
        (.anySubtype (.targetReference 1) .dwarf)
        [
          .optional (.controller .this)
            (.attach
              (.selected
                (.controller .this)
                (.range 1 1)
                (.intersection [
                  .permanent,
                  .subtype .equipment,
                  .controlled (.controller .this)]))
              (.targetReference 1))
        ]]]
#guard parseOracleParts (name := "Confusticate and Bebother")
  "Choose one —\n• Counter target spell unless its controller pays {4}.\n• Draw two cards, then discard a card." ==
  some [.actions [
    .chooseUniqueModes (.range 1 1) [
      .preventable (.controller (.targetReference 1)) [.mana [.generic 4]]
        (.counter (.target 1 .spell)),
      .sequence [
        .draw (.controller .this) 2,
        .discard (.controller .this) 1]]]]
#guard parseOracleParts (name := "")
  "Choose one —\n• Counter target spell unless its controller pays {4}.\n• Gain control of target creature." == none
#guard parseOracleParts (name := "")
  "Counter target spell unless its controller pays {4}." == none
#guard parseOracleParts (name := "") "" == some []
#guard parseOracleParts (name := "") "(This is reminder text.)" == some []
#guard parseOracleParts (name := "") "Lifelink\nDraw a card." ==
  some [.ability (.keyword .lifelink),
   .actions
     [.draw (.controller .this) (.nat 1)]]
#guard parseOracleParts (name := "") "Scry 2. Draw a card." ==
  some [.actions
     [.scry (.controller .this) (.nat 2),
      .draw (.controller .this) (.nat 1)]]
#guard parseOracleParts (name := "")
  "Untap target creature you control. Draw a card." ==
  some [.actions
     [.untap
        (.target
          1
          (.intersection
            [.permanent,
             .cardType .creature,
             .controlled (.controller .this)])),
      .draw (.controller .this) (.nat 1)]]
#guard parseOracleParts (name := "")
  "Flying\n//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure\nDraw a card." == none
#guard parseOracleParts (name := "") "//ADV//\nSpew Flame {Z}\nSorcery — Adventure" == none
#guard parseOracleParts (name := "") "//ADV//\nSpew Flame {4}{R}\nNot a type" == none
#guard parseOracleParts (name := "")
  "Choose one —\n• Gain control of target creature.\n• Draw two cards, then discard a card." == none
#guard parseOracleParts (name := "Thranduil's Decree")
  "Counter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled." ==
  some [.actions [
    .actionId 1 (.counter (.target 1 .spell)),
    .continuous
      [.replace
        (.putToGraveyard (.intersection [.wasObjectOfAction 1, .permanentSpell]))
        [.actionId 2 (.exile (.replacingObject)),
          .continuous
            [.canCastWithoutPayingManaCost (.controller .this) (.wasCreatedByAction 2)]
            .endOfGame]]
      .endOfGame]]
#guard parseOracleParts (name := "") "Counter target spell." == none
#guard parseOracleParts (name := "Thranduil's Decree")
  "Counter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. Draw a card." == none
#guard parseOracleParts (name := "Bilbo, Luckwearer") "Bilbo can't be blocked." ==
  some [.ability (.static (.forbid (.block .any .this)))]
#guard parseOracleParts (name := "") "This creature can't be blocked." ==
  some [.ability (.static (.forbid (.block .any .this)))]
#guard parseOracleParts (name := "Gandalf") "Bilbo can't be blocked." == none
#guard parseOracleParts (name := "Bilbo, Luckwearer")
  "Bilbo can't be blocked by Goblins." == none
#guard parseOracleParts (name := "Bilbo, Luckwearer")
  "Whenever Bilbo deals combat damage to a player, draw a card, then discard a card." ==
  some [.ability (
    .triggered
      (.combatDamage .this .player)
      (.sequence [
        .draw (.controller .this) 1,
        .discard (.controller .this) 1]))]
#guard parseOracleParts (name := "Gandalf")
  "Whenever Bilbo deals combat damage to a player, draw a card, then discard a card." == none
#guard parseOracleParts (name := "Bilbo, Luckwearer")
  "Whenever Bilbo deals combat damage to a player, draw a card." ==
  some [.ability
     (.triggered
       (.combatDamage .this .player)
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "")
  "Exchange control of two target nonland permanents that share a card type." ==
  some [.actions [
    .exchangeControl
      (.targetSet
        1
        (.range 2 2)
        (.intersection [.permanent, .not .land])
        [.shareCardType])]]
#guard parseOracleParts (name := "")
  "Exchange control of one target nonland permanent that share a card type." == none
#guard parseOracleParts (name := "")
  "Exchange control of 0 target nonland permanents that share a card type." == none
#guard parseOracleParts (name := "")
  "Exchange control of two target creatures that share a card type." == none
#guard parseOracleParts (name := "Bilbo, Luckwearer")
  "Bilbo can't be blocked.\nWhenever Bilbo deals combat damage to a player, draw a card, then discard a card.\n//ADV//\nBurglar's Plot {4}{U}\nSorcery — Adventure\nExchange control of two target nonland permanents that share a card type. (Then exile this card. You may cast the creature later from exile.)" ==
  some [
    .ability (.static (.forbid (.block .any .this))),
    .ability (
      .triggered
        (.combatDamage .this .player)
        (.sequence [
          .draw (.controller .this) 1,
          .discard (.controller .this) 1])),
    .alternative [
      .name "Burglar's Plot",
      .manaCost [.generic 4, .mono .blue],
      .type .sorcery,
      .subtype .adventure,
      .actions [
        .exchangeControl
          (.targetSet
            1
            (.range 2 2)
            (.intersection [.permanent, .not .land])
            [.shareCardType])]]]
#guard parseOracleParts (name := "")
  "Target creature's owner puts it on their choice of the top or bottom of their library." ==
  some [.actions [
    .playerSelectAction (.owner (.targetReference 1)) (.range 1 1)
      [.putOnTopOfLibrary
        (.target 1 (.intersection [.permanent, .cardType .creature])),
        .putOnBottomOfLibrary (.targetReference 1)]]]
#guard parseOracleParts (name := "")
  "When this creature dies, target creature an opponent controls gets -1/-1 until end of turn." ==
  some [.ability (
    .triggered
      (.die .this)
      (.continuous
        [.addPower
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.opponent (.controller .this))])) (Value.int (-1)),
         .addToughness
          (.targetReference 1) (Value.int (-1))]
        .endOfTurn))]
#guard parseOracleParts (name := "Front Porch Sentries")
  "When Front Porch Sentries dies, target creature an opponent controls gets -1/-1 until end of turn." ==
  some [.ability (
    .triggered
      (.die .this)
      (.continuous
        [.addPower
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.opponent (.controller .this))])) (Value.int (-1)),
         .addToughness
          (.targetReference 1) (Value.int (-1))]
        .endOfTurn))]
#guard parseOracleParts (name := "")
  "When this creature dies, target creature an opponent controls gets +1/+1 until end of turn." ==
  some [.ability (
    .triggered
      (.die .this)
      (.continuous
        [.addPower
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.opponent (.controller .this))])) (Value.int 1),
         .addToughness
          (.targetReference 1) (Value.int 1)]
        .endOfTurn))]
#guard parseOracleParts (name := "Gandalf")
  "When Front Porch Sentries dies, target creature an opponent controls gets -1/-1 until end of turn." == none
#guard parseOracleParts (name := "")
  "When another creature dies, target creature an opponent controls gets -1/-1 until end of turn." == none
#guard parseOracleParts (name := "")
  "Whenever this creature dies, target creature an opponent controls gets -1/-1 until end of turn." ==
  some [.ability
     (.triggered
       (.die .this)
       (.continuous
         [.addPower
            (.target
              1
              (.intersection
                [.permanent,
                 .cardType .creature,
                 .controlled
                   (.opponent (.controller .this))]))
            (.int (-1)),
          .addToughness (.targetReference 1) (.int (-1))]
         .endOfTurn))]
#guard parseOracleParts (name := "")
  "When this creature dies, target creature you control gets -1/-1 until end of turn." ==
  some [.ability
     (.triggered
       (.die .this)
       (.continuous
         [.addPower
            (.target
              1
              (.intersection
                [.permanent,
                 .cardType .creature,
                 .controlled (.controller .this)]))
            (.int (-1)),
          .addToughness (.targetReference 1) (.int (-1))]
         .endOfTurn))]
#guard parseOracleParts (name := "")
  "When this creature dies, target creature an opponent controls gets -1/-1." == none
#guard parseOracleParts (name := "")
  "When this creature dies, draw a card." ==
  some [.ability
     (.triggered
       (.die .this)
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "")
  "Whenever one or more other creatures die, scry 1." ==
  some [.ability (
    .triggered
      (.dieSimultaneously (.intersection [.not .this, .permanent, .cardType .creature]) [])
      (.scry (.controller .this) 1))]
#guard parseOracleParts (name := "Great Fierce Bee")
  "Whenever one or more other creatures die, scry 1. (Look at the top card of your library. You may put that card on the bottom.)" ==
  some [.ability (
    .triggered
      (.dieSimultaneously (.intersection [.not .this, .permanent, .cardType .creature]) [])
      (.scry (.controller .this) 1))]
#guard parseOracleParts (name := "")
  "Whenever one or more other creatures die, scry 2." ==
  some [.ability (
    .triggered
      (.dieSimultaneously (.intersection [.not .this, .permanent, .cardType .creature]) [])
      (.scry (.controller .this) 2))]
#guard parseOracleParts (name := "Great Fierce Bee")
  "Flying\nWhenever one or more other creatures die, scry 1. (Look at the top card of your library. You may put that card on the bottom.)" ==
  some [
    .ability (.keyword .flying),
    .ability (
      .triggered
        (.dieSimultaneously (.intersection [.not .this, .permanent, .cardType .creature]) [])
        (.scry (.controller .this) 1))]
#guard parseOracleParts (name := "")
  "Whenever one or more creatures die, scry 1." == none
#guard parseOracleParts (name := "")
  "Whenever one or more other creatures you control die, scry 1." == none
#guard parseOracleParts (name := "")
  "When one or more other creatures die, scry 1." == none
#guard parseOracleParts (name := "")
  "Whenever another creature dies, scry 1." == none
#guard parseOracleParts (name := "")
  "Whenever one or more other creatures die, draw a card." == none
#guard parseOracleParts (name := "")
  "Whenever one or more other creatures die, scry 0." == none
#guard parseOracleParts (name := "")
  "Whenever one or more other creatures die." == none
#guard parseOracleParts (name := "")
  "Target spell's owner puts it on their choice of the top or bottom of their library." == none
#guard parseOracleParts (name := "")
  "Target creature's owner puts it on top of their library." == none
#guard parseOracleParts (name := "Uneasy Partings")
  "This spell costs {1} less to cast if it targets an attacking nontoken creature.\nTarget creature's owner puts it on their choice of the top or bottom of their library." ==
  some [
    .ability (
      .stackStatic
        (.if
          (.targetsIncludeAny
            .this
            (.intersection [
              .permanent,
              .cardType .creature,
              .attacking .all,
              .not .token]))
          [.reduceCost .this [.mana [.generic 1]]])),
    .actions [
      .playerSelectAction (.owner (.targetReference 1)) (.range 1 1)
        [.putOnTopOfLibrary
          (.target 1 (.intersection [.permanent, .cardType .creature])),
          .putOnBottomOfLibrary (.targetReference 1)]]]
#guard parseOracleParts (name := "") "Destroy target creature." ==
  some [.actions [
    .destroy (.target 1 (.intersection [.permanent, .cardType .creature]))]]
#guard parseOracleParts (name := "") "Destroy target spell." == none
#guard parseOracleParts (name := "") "Destroy target creature with flying." ==
  some [.actions [
    .destroy
      (.target 1
        (.intersection [
          .permanent,
          .cardType .creature,
          .keyword .flying]))]]
#guard parseOracleParts (name := "") "Destroy target creature with power 4 or greater." ==
  some [.actions [
    .destroy
      (.target 1
        (.intersection [
          .permanent,
          .cardType .creature,
          .powerAtLeast (Value.int 4)]))]]
#guard parseOracleParts (name := "") "Destroy target creature with power 0 or greater." == none
#guard parseOracleParts (name := "") "Destroy target creature with power 4 or less." ==
  some [.actions [
    .destroy
      (.target 1
        (.intersection [
          .permanent,
          .cardType .creature,
          .powerAtMost (Value.int 4)]))]]
#guard parseOracleParts (name := "") "Destroy target creature with power 4." == none
#guard parseOracleParts (name := "") "Destroy target creature with haste and flying." == none
#guard parseOracleParts (name := "")
  "As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}." ==
  some [.ability (.stackStatic (
    .additionalCost .this
      [.or [
        .sacrificeCount
          (.intersection [
            .permanent,
            .union [.cardType .artifact, .cardType .creature]])
          1,
        .mana [.generic 4]]]))]
#guard parseOracleParts (name := "")
  "As an additional cost to cast this spell, sacrifice an artifact or creature." ==
  some [.ability
     (.stackStatic
       (.additionalCost
         .this
         [.sacrificeCount
            (.intersection
              [.permanent,
               .union
                 [.cardType .artifact,
                  .cardType .creature]])
            1]))]
#guard parseOracleParts (name := "")
  "As an additional cost to cast this spell, sacrifice artifact or creature or pay {4}." == none
#guard parseOracleParts (name := "")
  "As an additional cost to cast this spell, discard a card or pay {4}." ==
  some [.ability (.stackStatic (.additionalCost .this [.or [
    .discard (.selected (.controller .this) (.range 1 1) (.intersection [.inHand, .owner (.controller .this)])),
    .mana [.generic 4]]]))]
#guard parseOracleParts (name := "")
  "As an additional cost to cast this spell, discard two cards or pay {4}." == none
#guard parseOracleParts (name := "")
  "As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}{B}." == none
#guard parseOracleParts (name := "Stir Up Trouble")
  "As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}.\nDestroy target creature." ==
  some [
    .ability (.stackStatic (
      .additionalCost .this
        [.or [
          .sacrificeCount
            (.intersection [
              .permanent,
              .union [.cardType .artifact, .cardType .creature]])
            1,
          .mana [.generic 4]]])),
    .actions [
      .destroy
        (.target 1 (.intersection [.permanent, .cardType .creature]))]]
#guard parseOracleParts (name := "Desolation Prowler")
  "Pay 2 life: This creature gets +2/+2 until end of turn. Activate only once each turn." ==
  some [.ability (
    .abilityId 1
      (.activatedIf
        (.didNotHappen (.abilityWithIdActivated 1) .turnStart)
        [.life 2]
        (.continuous
          [.addPower (.source .this) (Value.int 2),
           .addToughness (.source .this) (Value.int 2)]
          .endOfTurn)))]
#guard parseOracleParts (name := "")
  "Pay 2 life: This creature gets +2/+2 until end of turn." ==
  some [.ability (
    .activated
      [.life 2]
      (.continuous
        [.addPower (.source .this) (Value.int 2),
         .addToughness (.source .this) (Value.int 2)]
        .endOfTurn))]
#guard parseOracleParts (name := "")
  "Pay 2 life: This creature gets +2/+2 until end of turn. Activate only twice each turn." == none
#guard parseOracleParts (name := "")
  "Pay 0 life: This creature gets +2/+2 until end of turn." == none
#guard parseOracleParts (name := "") "Pay 2 life: Draw a card." ==
  some [.ability
     (.activated
       [.life 2]
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "Ravening Warg")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life." ==
  some [.ability (
    .triggeredWhile
      (.attack .this .all)
      (.any
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this),
          .powerAtLeast (Value.int 4)]))
      (.gainLife (.controller .this) 2))]
#guard parseOracleParts (name := "Ravening Warg")
  "Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life." ==
  parseOracleParts (name := "Ravening Warg")
    "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life."
#guard parseOracleParts (name := "")
  "Whenever this creature attacks while you control a creature with power 3 or greater, you gain 2 life." == none
#guard parseOracleParts (name := "")
  "Landfall — Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life." == none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks, you gain 2 life." == none
#guard parseOracleParts (name := "")
  "Put a +1/+1 counter on up to one target creature. Target player gains 2 life." ==
  some [.actions [
    .putCounter
      (.targets 1 (.range 0 1) (.intersection [.permanent, .cardType .creature]))
      .plusOnePlusOne
      1,
    .gainLife (.target 2 .player) 2]]
#guard parseOracleParts (name := "") "Put a +1/+1 counter on target creature." ==
  some [.actions
     [.putCounter
        (.target
          1
          (.intersection
            [.permanent, .cardType .creature]))
        .plusOnePlusOne
        1]]
#guard parseOracleParts (name := "")
  "Put two +1/+1 counters on up to one target creature." ==
  some [.actions
     [.putCounter
        (.targets
          1
          (.range (.nat 0) (.nat 1))
          (.intersection
            [.permanent, .cardType .creature]))
        .plusOnePlusOne
        2]]
#guard parseOracleParts (name := "") "Target opponent gains 2 life." == none
#guard parseOracleParts (name := "") "You gain 0 life." == none
#guard parseOracleParts (name := "") "You gain 2 life." ==
  some [.actions [.gainLife (.controller .this) 2]]
#guard parseOracleParts (name := "Gollum, Silent Slinker")
  "Menace (This creature can't be blocked except by two or more creatures.)\n//ADV//\nMeager Meal {B}\nSorcery — Adventure\nPut a +1/+1 counter on up to one target creature. Target player gains 2 life. (Then exile this card. You may cast the creature later from exile.)" ==
  some [
    .ability (.keyword .menace),
    .alternative [
      .name "Meager Meal",
      .manaCost [.mono .black],
      .type .sorcery,
      .subtype .adventure,
      .actions [
        .putCounter
          (.targets 1 (.range 0 1) (.intersection [.permanent, .cardType .creature]))
          .plusOnePlusOne
          1,
        .gainLife (.target 2 .player) 2]]]
#guard parseOracleParts (name := "Dreaded Bat-Cloud")
  "This spell costs {3} less to cast if a creature died this turn.\nFlying, deathtouch" ==
  some [
    .ability (
      .stackStatic
        (.if
          (.happened (.die (.cardType .creature)) .turnStart)
          [.reduceCost .this [.mana [.generic 3]]])),
    .ability (.keyword .flying),
    .ability (.keyword .deathtouch)]
#guard parseOracleParts (name := "")
  "This spell costs {3} less to cast if a creature you control died this turn." == none
#guard parseOracleParts (name := "")
  "This spell costs {3} less to cast if two creatures died this turn." == none
#guard parseOracleParts (name := "")
  "When this Equipment enters, target opponent sacrifices a creature of their choice." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.sacrifice
        (.selected
          (.target 1 (.opponent (.controller .this)))
          (.range 1 1)
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.targetReference 1)]))))]
#guard parseOracleParts (name := "Crude Bent Blade")
  "When Crude Bent Blade enters, target opponent sacrifices a creature of their choice." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.sacrifice
        (.selected
          (.target 1 (.opponent (.controller .this)))
          (.range 1 1)
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.targetReference 1)]))))]
#guard parseOracleParts (name := "Gandalf")
  "When Crude Bent Blade enters, target opponent sacrifices a creature of their choice." == none
#guard parseOracleParts (name := "")
  "When this Equipment enters, target opponent sacrifices a creature." == none
#guard parseOracleParts (name := "")
  "When another Equipment enters, target opponent sacrifices a creature of their choice." == none
#guard parseOracleParts (name := "")
  "When this Equipment enters, target opponent sacrifices an artifact of their choice." == none
#guard parseOracleParts (name := "") "Equipped creature gets +2/+1." ==
  some [.ability (.static (.addPower (.hostOf .this) (Value.int 2))),
.ability (.static (.addToughness (.hostOf .this) (Value.int 1)))]
#guard parseOracleParts (name := "") "Equipped creature gets +2/+1 until end of turn." == none
#guard parseOracleParts (name := "") "Equipped creature gets +2/+1 and has flying." ==
  some [
    .ability (.static (.addPower (.hostOf .this) (Value.int 2))),
    .ability (.static (.addToughness (.hostOf .this) (Value.int 1))),
    .ability (.static (.gainAbility (.hostOf .this) (.keyword .flying)))]
#guard parseOracleParts (name := "") "Equipped creature gets +1/+0 and has menace." ==
  some [
    .ability (.static (.addPower (.hostOf .this) (Value.int 1))),
    .ability (.static (.gainAbility (.hostOf .this) (.keyword .menace)))]
#guard parseOracleParts (name := "") "Equipped creature gets +0/+0 and has menace." == none
#guard parseOracleParts (name := "") "Equipped creature gets +1/+0 and gains menace." == none
#guard parseOracleParts (name := "")
  "Equipped creature gets +1/+0 and has menace until end of turn." == none
#guard parseOracleParts (name := "") "Equip {2}" ==
  some [.ability (.keywordWithCost .equip [.mana [.generic 2]])]
#guard parseOracleParts (name := "")
  "Equip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)" ==
  some [.ability (.keywordWithCost .equip [.mana [.generic 2]])]
#guard parseOracleParts (name := "") "Equip" == none
#guard parseOracleParts (name := "") "Equip {2}: Draw a card." == none
#guard parseOracleParts (name := "Crude Bent Blade")
  "When this Equipment enters, target opponent sacrifices a creature of their choice.\nEquipped creature gets +2/+1.\nEquip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)" ==
  some [
    .ability (
      .triggered
        (.enter .this)
        (.sacrifice
          (.selected
            (.target 1 (.opponent (.controller .this)))
            (.range 1 1)
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.targetReference 1)])))),
    .ability (.static (.addPower (.hostOf .this) (Value.int 2))),
    .ability (.static (.addToughness (.hostOf .this) (Value.int 1))),
    .ability (.keywordWithCost .equip [.mana [.generic 2]])]

#guard parseOracleParts (name := "Gollum the Abandoned") "Gollum can't block." ==
  some [.ability (.static (.forbid (.block .this .any)))]
#guard parseOracleParts (name := "Gollum the Abandoned") "When Gollum enters, draw a card." ==
  some [.ability (.triggered (.enter .this) (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "Gandalf") "Gollum can't block." == none
#guard parseOracleParts (name := "Gandalf") "When Gollum enters, draw a card." == none
#guard parseOracleParts (name := "") "This creature can't block." ==
  some [.ability (.static (.forbid (.block .this .any)))]
#guard parseOracleParts (name := "") "This creature can't block unless you control a Goblin." ==
  some [.ability (.static (.if
    (.not (.any (.intersection [.permanent, .subtype .goblin, .controlled (.controller .this)])))
    [.forbid (.block .this .any)]))]
#guard parseOracleParts (name := "") "This creature can't block unless you control a Gandalf." ==
  none
#guard parseOracleParts (name := "Gollum the Abandoned")
  "When Gollum enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.sequence [
        .exile
          (.targets 1 (.range 0 1)
            (.intersection [.inGraveyard, .owner (.opponent (.controller .this))])),
        .loseLife (.opponent (.controller .this)) 2]))]
#guard parseOracleParts (name := "")
  "When this creature enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.sequence [
        .exile
          (.targets 1 (.range 0 1)
            (.intersection [.inGraveyard, .owner (.opponent (.controller .this))])),
        .loseLife (.opponent (.controller .this)) 2]))]
#guard parseOracleParts (name := "Gollum the Abandoned")
  "When Bilbo enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life." ==
  none
#guard parseOracleParts (name := "")
  "When this creature enters, exile up to one target creature card from an opponent's graveyard. Each opponent loses 2 life." ==
  none
#guard parseOracleParts (name := "")
  "{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand. Activate only as a sorcery." ==
  some [.ability (
    .graveyardActivatedIf
      (.timeToCastSorcery (.controller .this))
      [.mana [.generic 2],
        .sacrificeCount
          (.intersection [
            .permanent,
            .union [.cardType .artifact, .cardType .creature]])
          1]
      (.returnToHand (.intersection [.inGraveyard, .source .this])))]
#guard parseOracleParts (name := "")
  "{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand." ==
  some [.ability
     (.activated
       [.mana [.generic 2],
        .sacrificeCount
          (.intersection
            [.permanent,
             .union
               [.cardType .artifact,
                .cardType .creature]])
          1]
       (.returnToHand
         (.intersection
           [.inGraveyard, .source .this])))]
#guard parseOracleParts (name := "")
  "{2}: Return this card from your graveyard to the battlefield." == none
#guard parseOracleParts (name := "Gollum the Abandoned")
  "Gollum can't block.\nWhen Gollum enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life.\n{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand. Activate only as a sorcery." ==
  some [
    .ability (.static (.forbid (.block .this .any))),
    .ability (
      .triggered
        (.enter .this)
        (.sequence [
          .exile
            (.targets 1 (.range 0 1)
              (.intersection [.inGraveyard, .owner (.opponent (.controller .this))])),
          .loseLife (.opponent (.controller .this)) 2])),
    .ability (
      .graveyardActivatedIf
        (.timeToCastSorcery (.controller .this))
        [.mana [.generic 2],
          .sacrificeCount
            (.intersection [
              .permanent,
              .union [.cardType .artifact, .cardType .creature]])
            1]
        (.returnToHand (.intersection [.inGraveyard, .source .this])))]

#guard parseOracleParts (name := "")
  "Target creature gets +2/+2 and gains lifelink until end of turn." ==
  some [.actions [
    .continuous
      [.addPower
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        (Value.int 2),
       .addToughness
        (.targetReference 1)
        (Value.int 2),
       .gainAbility (.targetReference 1) (.keyword .lifelink)]
      .endOfTurn]]
#guard parseOracleParts (name := "")
  "Target creature gets +2/+2 and has lifelink until end of turn." == none
#guard parseOracleParts (name := "") "Target creature gets +0/+0 until end of turn." == none
#guard parseOracleParts (name := "") "Target creature gets +0/+1 until end of turn." ==
  some [.actions [
    .continuous
      [.addToughness
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        (Value.int 1)]
      .endOfTurn]]
#guard parseOracleParts (name := "")
  "{W}: This creature gets +0/+0 until end of turn." == none
#guard parseOracleParts (name := "")
  "Target creature gets -5/-5 until end of turn. If that creature would die this turn, exile it instead." ==
  some [.actions [
    .continuous
      [.addPower
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        (Value.int (-5)),
       .addToughness
        (.targetReference 1)
        (Value.int (-5)),
       .replace
         (.putToGraveyard (.targetReference 1))
         [.exile (.replacingObject)]]
      .endOfTurn]]
#guard parseOracleParts (name := "")
  "Target creature gets -5/-5 until end of turn. Exile it instead." == none
#guard parseOracleParts (name := "")
  "Creatures target player controls get -1/-1 until end of turn." ==
  some [.actions [
    .continuous
      [.addPower
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.target 1 .player)])
        (Value.int (-1)),
       .addToughness
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.targetReference 1)])
        (Value.int (-1))]
      .endOfTurn]]
#guard parseOracleParts (name := "")
  "Creatures target player controls get -1/-1." == none
#guard parseOracleParts (name := "")
  "Target player draws two cards and loses 2 life." ==
  some [.actions [
    .sequence [
      .draw (.target 1 .player) 2,
      .loseLife (.targetReference 1) 2]]]
#guard parseOracleParts (name := "")
  "Target player draws two cards and gains 2 life." == none
#guard parseOracleParts (name := "")
  "Choose one —\n• Target creature gets -5/-5 until end of turn. If that creature would die this turn, exile it instead.\n• Creatures target player controls get -1/-1 until end of turn." ==
  some [.actions [
    .chooseUniqueModes (.range 1 1) [
      .continuous
        [.addPower
          (.target 1 (.intersection [.permanent, .cardType .creature]))
          (Value.int (-5)),
         .addToughness
          (.targetReference 1)
          (Value.int (-5)),
         .replace
           (.putToGraveyard (.targetReference 1))
           [.exile (.replacingObject)]]
        .endOfTurn,
      .continuous
        [.addPower
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.target 2 .player)])
          (Value.int (-1)),
         .addToughness
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.targetReference 2)])
          (Value.int (-1))]
        .endOfTurn]]]
#guard parseOracleParts (name := "")
  "Choose one —\n• Target player draws two cards and loses 2 life.\n• Target creature gets +2/+2 and gains lifelink until end of turn." ==
  some [.actions [
    .chooseUniqueModes (.range 1 1) [
      .sequence [
        .draw (.target 1 .player) 2,
        .loseLife (.targetReference 1) 2],
      .continuous
        [.addPower
          (.target 2 (.intersection [.permanent, .cardType .creature]))
          (Value.int 2),
         .addToughness
          (.targetReference 2)
          (Value.int 2),
         .gainAbility (.targetReference 2) (.keyword .lifelink)]
        .endOfTurn]]]
#guard parseOracleParts (name := "")
  "Choose one —\n• Target creature gets -5/-5 until end of turn. If that creature would die this turn, exile it instead.\n• Gain control of target creature." ==
  none
#guard parseOracleParts (name := "")
  "When this creature enters, each opponent discards a card." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.discard (.opponent (.controller .this)) 1))]
#guard parseOracleParts (name := "")
  "When another creature enters, each opponent discards a card." ==
  some [.ability (
    .triggered
      (.enter (.intersection [.not .this, .permanent, .cardType .creature]))
      (.discard (.opponent (.controller .this)) (.nat 1)))]
#guard parseOracleParts (name := "")
  "When this creature enters, each opponent discards a card of their choice." == none
#guard parseOracleParts (name := "Gandalf, Spark Starter")
  "When Gandalf enters, he deals 3 damage divided as you choose among one, two, or three targets." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.divideDamage
        (.controller .this)
        (.source .this)
        (.targets 1 (.range 1 3) .all)
        3))]
#guard parseOracleParts (name := "Gandalf, Spark Starter")
  "Reach\nWhen Gandalf enters, he deals 3 damage divided as you choose among one, two, or three targets." ==
  some [
    .ability (.keyword .reach),
    .ability (
      .triggered
        (.enter .this)
        (.divideDamage
          (.controller .this)
          (.source .this)
          (.targets 1 (.range 1 3) .all)
          3))]
#guard parseOracleParts (name := "Gandalf")
  "When Bilbo enters, he deals 3 damage divided as you choose among one, two, or three targets." ==
  none
#guard parseOracleParts (name := "Gandalf, Spark Starter")
  "When Gandalf enters, Bilbo deals 3 damage divided as you choose among one, two, or three targets." ==
  none
#guard parseOracleParts (name := "Gandalf, Spark Starter")
  "When Gandalf enters, he deals 3 damage divided as you choose among one or four targets." == none
#guard parseOracleParts (name := "Gandalf, Spark Starter")
  "When Gandalf enters, he deals 0 damage divided as you choose among one, two, or three targets." ==
  none
#guard parseOracleParts (name := "Gandalf, Spark Starter")
  "When Gandalf enters, he deals 3 damage divided as you choose among one, two, or three target creatures." ==
  none
#guard parseOracleParts (name := "")
  "When this Equipment enters, you may discard a card. If you do, draw two cards." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.sequence [
        .optional (.controller .this)
          (.actionId 1 (.discard (.controller .this) 1)),
        .if (.happened (.actionWithId 1) .gameStart) [.draw (.controller .this) 2]]))]
#guard parseOracleParts (name := "")
  "When this Equipment enters, you may discard a card. Draw two cards." == none
#guard parseOracleParts (name := "")
  "When this Equipment enters, discard a card. If you do, draw two cards." == none
#guard parseOracleParts (name := "")
  "When this Equipment enters, you may discard a card. If you do, draw two cards.\nEquipped creature gets +2/+0.\nEquip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)" ==
  some [
    .ability (
      .triggered
        (.enter .this)
        (.sequence [
          .optional (.controller .this)
            (.actionId 1 (.discard (.controller .this) 1)),
          .if (.happened (.actionWithId 1) .gameStart) [.draw (.controller .this) 2]])),
    .ability (.static (.addPower (.hostOf .this) (Value.int 2))),
    .ability (.keywordWithCost .equip [.mana [.generic 3]])]
#guard parseOracleParts (name := "Smaug, the Great Calamity")
  "Flying\n//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure\nSpew Flame deals 5 damage to target creature. (Then exile this card. You may cast the creature later from exile.)" ==
  some [
    .ability (.keyword .flying),
    .alternative [
      .name "Spew Flame",
      .manaCost [.generic 4, .mono .red],
      .type .sorcery,
      .subtype .adventure,
      .actions [
        .dealDamage
          .this
          (.target 1 (.intersection [.permanent, .cardType .creature]))
          (.nat 5)]]]

#guard parseOracleParts (name := "")
  "{5}{G}{G}: Put three +1/+1 counters on this creature." ==
  some [.ability (
    .activated
      [.mana [.generic 5, .mono .green, .mono .green]]
      (.putCounter (.source .this) .plusOnePlusOne 3))]
#guard parseOracleParts (name := "")
  "{1}: Put a +1/+1 counter on this creature." ==
  some [.ability (
    .activated [.mana [.generic 1]] (.putCounter (.source .this) .plusOnePlusOne 1))]
#guard parseOracleParts (name := "")
  "{1}: Put three +1/+1 counter on this creature." == none
#guard parseOracleParts (name := "")
  "{1}: Put a +1/+1 counters on this creature." == none
#guard parseOracleParts (name := "")
  "{1}: Put three +1/+1 counters on target creature." ==
  some [.ability
     (.activated
       [.mana [.generic 1]]
       (.putCounter
         (.target
           1
           (.intersection
             [.permanent, .cardType .creature]))
         .plusOnePlusOne
         3))]
#guard parseOracleParts (name := "")
  "Sacrifice another creature or artifact: Exile the top card of your library. You may play it until the end of your next turn. Activate only during your turn and only once each turn." ==
  some [.ability (
    .abilityId 1
      (.activatedIf
        (.and
          (.turn (.controller .this))
          (.didNotHappen (.abilityWithIdActivated 1) .turnStart))
        [.sacrificeCount
          (.intersection [
            .not .this,
            .permanent,
            .union [.cardType .creature, .cardType .artifact]])
          1]
        (.sequence [
          .actionId 1 (.exile (.topOfLibrary (.controller .this) 1)),
          .continuous
            [.canPlay (.controller .this) (.wasCreatedByAction 1)]
            (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])])))]
#guard parseOracleParts (name := "")
  "Sacrifice a creature or artifact: Exile the top card of your library. You may play it until the end of your next turn. Activate only during your turn and only once each turn." ==
  none
#guard parseOracleParts (name := "")
  "Sacrifice another creature or artifact: Exile the top card of your library. You may play it until end of turn. Activate only during your turn and only once each turn." ==
  none
#guard parseOracleParts (name := "")
  "Target creature you control deals damage equal to its power to target creature an opponent controls." ==
  some [.actions [
    .dealDamageEqualToPower
      (.target 1
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)]))
      (.target 2
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.opponent (.controller .this))]))]]
#guard parseOracleParts (name := "")
  "Target creature deals damage equal to its power to target creature an opponent controls." ==
  none
#guard parseOracleParts (name := "Galion, Elvenking's Butler")
  "Whenever Galion attacks, choose up to one other target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn." ==
  some [.ability (
    .triggered
      (.attack .this .all)
      (.continuous
        [.setBasePower
          (.targets 1 (.range 0 1)
            (.intersection [
              .not .this,
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]))
          (Value.greatestPower (.source .this)),
         .setBaseToughness
          (.targetReference 1)
          (Value.greatestToughness (.source .this))]
        .endOfTurn))]
#guard parseOracleParts (name := "Galion, Elvenking's Butler")
  "Whenever this creature attacks, choose up to one other target creature you control. Its base power and toughness become equal to this creature's power and toughness until end of turn." ==
  parseOracleParts (name := "Galion, Elvenking's Butler")
    "Whenever Galion attacks, choose up to one other target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn."
#guard parseOracleParts (name := "Gandalf")
  "Whenever Galion attacks, choose up to one other target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn." ==
  none
#guard parseOracleParts (name := "Galion, Elvenking's Butler")
  "Whenever Galion attacks, choose up to one target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn." ==
  none
#guard parseOracleParts (name := "")
  "Choose one —\n• Destroy target creature with flying.\n• Put a +1/+1 counter on target creature you control. It gains trample and hexproof until end of turn. (It can't be the target of spells or abilities your opponents control.)" ==
  some [.actions [
    .chooseUniqueModes (.range 1 1) [
      .destroy
        (.target 1
          (.intersection [
            .permanent,
            .cardType .creature,
            .keyword .flying])),
      .sequence [
        .putCounter
          (.target 2
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]))
          .plusOnePlusOne
          1,
        .continuous
          [.gainAbility (.targetReference 2) (.keyword .trample),
            .gainAbility (.targetReference 2) (.keyword .hexproof)]
          .endOfTurn]]]]
#guard parseOracleParts (name := "")
  "Put a +1/+1 counter on target creature you control. It gets trample until end of turn." ==
  none
#guard parseOracleParts (name := "")
  "Choose one —\n• Put a +1/+1 counter on target creature you control." ==
  some [.actions
     [.chooseUniqueModes
        (.range (.nat 1) (.nat 1))
        [.putCounter
           (.target
             1
             (.intersection
               [.permanent,
                .cardType .creature,
                .controlled (.controller .this)]))
           .plusOnePlusOne
           1]]]
#guard parseOracleParts (name := "Beorn's Hospitality")
  "Landfall — Whenever a land you control enters, put a +1/+1 counter on target creature you control.\n{5}{G}{G}: This enchantment becomes a Bear creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\" (This effect doesn't end.)" ==
  some [
    .ability (
      .triggered
        (.enter
          (.intersection [
            .permanent,
            .cardType .land,
            .controlled (.controller .this)]))
        (.putCounter
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]))
          .plusOnePlusOne
          1)),
    .ability (
      .activated
        [.mana [.generic 5, .mono .green, .mono .green]]
        (.continuous
          [.gainType .this .creature,
            .gainSubtype .this .bear,
            .gainAbility
              .this
              (.static
                (.setPower
                  .this
                  (.count
                    (.intersection [
                      .permanent,
                      .cardType .land,
                      .controlled (.controller .this)])))),
            .gainAbility
              .this
              (.static
                (.setToughness
                  .this
                  (.count
                    (.intersection [
                      .permanent,
                      .cardType .land,
                      .controlled (.controller .this)]))))]
          .endOfGame))]
#guard parseOracleParts (name := "")
  "Whenever a land you control enters, put a +1/+1 counter on target creature you control." ==
  parseOracleParts (name := "")
    "Landfall — Whenever a land you control enters, put a +1/+1 counter on target creature you control."
#guard parseOracleParts (name := "")
  "{1}{G}: This enchantment becomes an Elf creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\"" ==
  some [.ability (
    .activated
      [.mana [.generic 1, .mono .green]]
      (.continuous
        [.gainType .this .creature,
          .gainSubtype .this .elf,
          .gainAbility
            .this
            (.static
              (.setPower
                .this
                (.count
                  (.intersection [
                    .permanent,
                    .cardType .land,
                    .controlled (.controller .this)])))),
          .gainAbility
            .this
            (.static
              (.setToughness
                .this
                (.count
                  (.intersection [
                    .permanent,
                    .cardType .land,
                    .controlled (.controller .this)]))))]
        .endOfGame))]
#guard parseOracleParts (name := "")
  "Landfall — Whenever a land enters, put a +1/+1 counter on target creature you control." == none
#guard parseOracleParts (name := "")
  "Whenever a land you control enters, put a +1/+1 counter on target creature." ==
  some [.ability
     (.triggered
       (.enter
         (.intersection
           [.permanent,
            .cardType .land,
            .controlled (.controller .this)]))
       (.putCounter
         (.target
           1
           (.intersection
             [.permanent, .cardType .creature]))
         .plusOnePlusOne
         1))]
#guard parseOracleParts (name := "Gandalf")
  "{5}{G}{G}: Beorn's Hospitality becomes a Bear creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\"" ==
  none
#guard parseOracleParts (name := "")
  "{5}{G}{G}: This enchantment becomes a Bear creature in addition to its other types and its power and toughness are each equal to the number of lands you control." ==
  none
#guard parseOracleParts (name := "")
  "{1}{G}: This enchantment becomes a Bear creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\" until end of turn." ==
  none
#guard englishSmall? " 2 " == some 2
#guard englishSmall? "Two" == some 2
#guard positiveCount "0" == none
#guard positiveCount " 3 " == some 3
#guard parseOracleParts (name := "") "When this creature enters, draw one card." ==
  parseOracleParts (name := "") "When this creature enters, draw a card."
#guard parseOracleParts (name := "") "When this creature enters, draw 1 card." ==
  parseOracleParts (name := "") "When this creature enters, draw a card."
#guard parseOracleParts (name := "") "When this creature enters, draw a cards." == none
#guard parseOracleParts (name := "") "When this creature enters, draw one cards." == none
#guard parseOracleParts (name := "")
  "Sacrifice a creature: This creature gets +1/+1 until end of turn." == none
#guard parseOracleParts (name := "") "Reach, trample, haste" ==
  some [
    .ability (.keyword .reach),
    .ability (.keyword .trample),
    .ability (.keyword .haste)]
#guard parseOracleParts (name := "") "Reach, deathtouch" ==
  some [.ability (.keyword .reach), .ability (.keyword .deathtouch)]
#guard parseOracleParts (name := "")
  "Whenever another Elf you control enters, this creature gets +1/+1 until end of turn." ==
  some [.ability (
    .triggered
      (.enter
        (.intersection [
          .not .this,
          .permanent,
          .subtype .elf,
          .controlled (.controller .this)]))
      (.continuous
        [.addPower (.source .this) (Value.int 1),
         .addToughness (.source .this) (Value.int 1)]
        .endOfTurn))]
#guard parseOracleParts (name := "")
  "Whenever another Bear you control enters, this creature gets +1/+1 until end of turn." ==
  some [.ability
     (.triggered
       (.enter
         (.intersection
           [.not .this,
            .permanent,
            .subtype .bear,
            .controlled (.controller .this)]))
       (.continuous
         [.addPower
            (.source .this)
            (.int 1),
          .addToughness
            (.source .this)
            (.int 1)]
         .endOfTurn))]
#guard parseOracleParts (name := "")
  "Whenever another Elf you control enters, this creature gets +2/+2 until end of turn." ==
  some [.ability
     (.triggered
       (.enter
         (.intersection
           [.not .this,
            .permanent,
            .subtype .elf,
            .controlled (.controller .this)]))
       (.continuous
         [.addPower
            (.source .this)
            (.int 2),
          .addToughness
            (.source .this)
            (.int 2)]
         .endOfTurn))]
#guard parseOracleParts (name := "")
  "Landfall — Whenever a land you control enters, this creature gets +1/+1 until end of turn." ==
  some [.ability (
    .triggered
      (.enter
        (.intersection [
          .permanent,
          .cardType .land,
          .controlled (.controller .this)]))
      (.continuous
        [.addPower (.source .this) (Value.int 1),
         .addToughness (.source .this) (Value.int 1)]
        .endOfTurn))]
#guard parseOracleParts (name := "")
  "Whenever a land you control enters, this creature gets +1/+1 until end of turn." ==
  parseOracleParts (name := "")
    "Landfall — Whenever a land you control enters, this creature gets +1/+1 until end of turn."
#guard parseOracleParts (name := "")
  "Landfall — Whenever a land you control enters, creatures you control get +1/+1 until end of turn." ==
  some [.ability
     (.triggered
       (.enter
         (.intersection
           [.permanent,
            .cardType .land,
            .controlled (.controller .this)]))
       (.continuous
         [.addPower
            (.intersection
              [.permanent,
               .cardType .creature,
               .controlled (.controller .this)])
            (.int 1),
          .addToughness
            (.intersection
              [.permanent,
               .cardType .creature,
               .controlled (.controller .this)])
            (.int 1)]
         .endOfTurn))]
#guard parseOracleParts (name := "Woodland Weavemaster")
  "{T}: Add X mana of any one color, where X is this creature's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources." ==
  some [.ability (
    .activated
      [.tapSymbol]
      (.sequence [
        .actionId 1
          (.addManaOfOneColor
            (.controller .this)
            ManaSymbol.anyColor
            (.greatestPower .this)),
        .continuous
          [.forbid
            (.spendManaCreatedByAction 1
              (.not
                (.or
                  (.castSpell (.subtype .elf))
                  (.activateAbility (.subtype .elf)))))]
          .endOfTurn]))]
#guard parseOracleParts (name := "Woodland Weavemaster")
  "{T}: Add X mana of any one color, where X is Woodland Weavemaster's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources." ==
  parseOracleParts (name := "Woodland Weavemaster")
    "{T}: Add X mana of any one color, where X is this creature's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources."
#guard parseOracleParts (name := "Gandalf")
  "{T}: Add X mana of any one color, where X is Woodland Weavemaster's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources." ==
  none
#guard parseOracleParts (name := "Mirkwood Pathmaker")
  "Mirkwood Pathmaker's power and toughness are each equal to the number of lands you control." ==
  some [
    .ability (
      .static
        (.setPower
          .this
          (.count
            (.intersection [
              .permanent,
              .cardType .land,
              .controlled (.controller .this)])))),
    .ability (
      .static
        (.setToughness
          .this
          (.count
            (.intersection [
              .permanent,
              .cardType .land,
              .controlled (.controller .this)]))))]
#guard parseOracleParts (name := "")
  "This creature's power and toughness are each equal to the number of lands you control." ==
  parseOracleParts (name := "Mirkwood Pathmaker")
    "Mirkwood Pathmaker's power and toughness are each equal to the number of lands you control."
#guard parseOracleParts (name := "Gandalf")
  "Mirkwood Pathmaker's power and toughness are each equal to the number of lands you control." ==
  none
#guard parseOracleParts (name := "") "You may play an additional land this turn." ==
  some [.actions [
    .continuous
      [.increaseLandPlayLimit (.controller .this) (Value.nat 1)]
      .endOfTurn]]
#guard parseOracleParts (name := "") "You may play two additional lands this turn." == none
#guard parseOracleParts (name := "")
  "When this creature enters, search your library for a Forest card, put that card onto the battlefield, then shuffle." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.searchLibraryThenShuffle
        (.controller .this)
        [.putOntoBattlefield
          (.selected
            (.controller .this)
            (.range 1 1)
            (.intersection [.inLibrary, .subtype .forest]))]))]
#guard parseOracleParts (name := "Wood Elves")
  "When Wood Elves enters, search your library for a Forest card, put that card onto the battlefield, then shuffle." ==
  parseOracleParts (name := "")
    "When this creature enters, search your library for a Forest card, put that card onto the battlefield, then shuffle."
#guard parseOracleParts (name := "")
  "When this creature enters, search your library for an Island card, put that card onto the battlefield, then shuffle." ==
  none
#guard parseOracleParts (name := "")
  "Trample\n//ADV//\nTill and Tend {1}{G}\nSorcery — Adventure\nYou may play an additional land this turn. (Then exile this card. You may cast the creature later from exile.)" ==
  some [
    .ability (.keyword .trample),
    .alternative [
      .name "Till and Tend",
      .manaCost [.generic 1, .mono .green],
      .type .sorcery,
      .subtype .adventure,
      .actions [
        .continuous
          [.increaseLandPlayLimit (.controller .this) (Value.nat 1)]
          .endOfTurn]]]
#guard parseOracleParts (name := "Elvenking's Halls") "This land enters tapped." ==
  some [.ability (.static (.replace (.enter .this)
    [.putOntoBattlefieldInState .this [.tapped]]))]
#guard parseOracleParts (name := "") "This spell enters tapped." == none
#guard parseOracleParts (name := "") "This land enters." == none
#guard parseOracleParts (name := "") "{T}: Add {G} or {U}." ==
  some [.ability (.activated [.tapSymbol]
    (.playerSelectAction (.controller .this) (.range 1 1)
      [.addMana (.controller .this) [.mono .green],
       .addMana (.controller .this) [.mono .blue]]))]
#guard parseOracleParts (name := "") "{T}: Add {G}." ==
  some [.ability
     (.activated
       [.tapSymbol]
       (.addMana
         (.controller .this)
         [.colored .green]))]
#guard parseOracleParts (name := "") "{T}: Add {2} or {G}." == none
#guard parseOracleParts (name := "")
  "{4}{U}: Target creature can't be blocked this turn." ==
  some [.ability (.activated [.mana [.generic 4, .mono .blue]]
    (.continuous
      [.forbid (.block .any
        (.target 1 (.intersection [.permanent, .cardType .creature])))]
      .endOfTurn))]
#guard parseOracleParts (name := "")
  "{2}{G}{U}, {T}, Sacrifice this land: Put two +1/+1 counters on target Elf you control. Activate only as a sorcery." ==
  some [.ability (.activatedIf (.timeToCastSorcery (.controller .this))
    [.mana [.generic 2, .mono .green, .mono .blue], .tapSymbol, .sacrifice .this]
    (.putCounter
      (.target 1 (.intersection
        [.permanent, .cardType .creature, .subtype .elf, .controlled (.controller .this)]))
      .plusOnePlusOne 2))]
#guard parseOracleParts (name := "")
  "{2}{B}{R}, {T}, Sacrifice this land: Put two +1/+1 counters on target Goblin or Orc you control. Activate only as a sorcery." ==
  some [.ability (.activatedIf (.timeToCastSorcery (.controller .this))
    [.mana [.generic 2, .mono .black, .mono .red], .tapSymbol, .sacrifice .this]
    (.putCounter
      (.target 1 (.intersection [
        .permanent, .cardType .creature,
        .union [.subtype .goblin, .subtype .orc],
        .controlled (.controller .this)]))
      .plusOnePlusOne 2))]
#guard parseOracleParts (name := "")
  "{2}{B}{G}, {T}, Sacrifice this land: Put two +1/+1 counter on target Bear, Spider, or Wolf you control. Activate only as a sorcery." ==
  none
#guard parseOracleParts (name := "")
  "{T}, Sacrifice this land: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle." ==
  some [.ability (.activated [.tapSymbol, .sacrifice .this]
    (.searchLibraryThenShuffle (.controller .this)
      [.putOntoBattlefieldInState
        (.selected (.controller .this) (.range 1 1)
          (.intersection [.inLibrary, .cardType .land, .supertype .basic]))
        [.tapped]]))]
#guard parseOracleParts (name := "")
  "Halflingcycling {4} ({4}, Discard this card: Search your library for a Halfling card, reveal it, put it into your hand, then shuffle.)" ==
  some [.ability (.keywordWithCost (.typecycling [] [] [.halfling]) [.mana [.generic 4]])]
#guard parseOracleParts (name := "") "Halflingcycling" == none
#guard parseOracleParts (name := "") "Cycling {2}" == none
#guard parseOracleParts (name := "") "Basic landcycling {2}" ==
  some [.ability (.keywordWithCost (.typecycling [.basic] [.land] []) [.mana [.generic 2]])]
#guard parseOracleParts (name := "")
  "When this Equipment enters, you gain 2 life." ==
  some [.ability (.triggered (.enter .this) (.gainLife (.controller .this) 2))]
#guard parseOracleParts (name := "")
  "When this Equipment enters, target player gains 2 life." ==
  some [.ability
     (.triggered
       (.enter .this)
       (.gainLife
         (.target 1 .player)
         (.nat 2)))]
#guard parseOracleParts (name := "")
  "When this creature enters, untap another target creature you control. If that creature is a Bear, put a +1/+1 counter on it." ==
  some [.ability (.triggered (.enter .this)
    (.sequence [
      .untap (.target 1 (.intersection [
        .not .this, .permanent, .cardType .creature, .controlled (.controller .this)])),
      .if (.anySubtype (.targetReference 1) .bear)
        [.putCounter (.targetReference 1) .plusOnePlusOne 1]]))]
#guard parseOracleParts (name := "")
  "When this creature enters, untap target creature you control. If that creature is a Bear, put a +1/+1 counter on it." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, this creature gets +2/+2 until end of turn." ==
  some [.ability (.triggeredWhile (.attack .this .all)
    (.any (.intersection [
      .permanent, .cardType .creature, .controlled (.controller .this),
      .powerAtLeast (Value.int 4)]))
    (.continuous
      [.addPower (.source .this) (Value.int 2), .addToughness (.source .this) (Value.int 2)]
      .endOfTurn))]
#guard parseOracleParts (name := "")
  "Whenever this creature attacks while you control a creature with power 4 or greater, this creature gets +2/+2 until end of turn." ==
  parseOracleParts (name := "")
    "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, this creature gets +2/+2 until end of turn."
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, creatures you control get +2/+2 until end of turn." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+0 and creatures you control gain trample." ==
  some [.ability (.triggeredWhile (.attack .this .all)
    (.any (.intersection [
      .permanent, .cardType .creature, .controlled (.controller .this),
      .powerAtLeast (Value.int 4)]))
    (.continuous
      [.addPower (.source .this) (Value.int 1),
        .gainAbility
          (.intersection [
            .permanent, .cardType .creature, .controlled (.controller .this)])
          (.keyword .trample)]
      .endOfTurn))]
#guard parseOracleParts (name := "")
  "Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+0 and creatures you control gain trample." ==
  parseOracleParts (name := "")
    "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+0 and creatures you control gain trample."
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +0/+0 and creatures you control gain trample." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+1 and creatures you control gain trample." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+0 and creatures you control gain haste." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, put a +1/+1 counter on each creature you control." ==
  some [.ability (.triggeredWhile (.attack .this .all)
    (.any (.intersection [
      .permanent, .cardType .creature, .controlled (.controller .this),
      .powerAtLeast (Value.int 4)]))
    (.putCounter
      (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this)])
      .plusOnePlusOne
      1))]
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, put two +1/+1 counters on each creature you control." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever you attack while you control a creature with power 4 or greater, you draw a card and lose 1 life." ==
  some [.ability (.triggeredWhile
    (.attackSimultaneously
      (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this)])
      .all
      [])
    (.any (.intersection [
      .permanent, .cardType .creature, .controlled (.controller .this),
      .powerAtLeast (Value.int 4)]))
    (.sequence [
      .draw (.controller .this) 1,
      .loseLife (.controller .this) 1]))]
#guard parseOracleParts (name := "")
  "Whenever you attack while you control a creature with power 4 or greater, you draw a card and lose 1 life." ==
  parseOracleParts (name := "")
    "Ferocious — Whenever you attack while you control a creature with power 4 or greater, you draw a card and lose 1 life."
#guard parseOracleParts (name := "")
  "Ferocious — Whenever you attack while you control a creature with power 4 or greater, you draw two cards and lose 1 life." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever you attack while you control a creature with power 4 or greater, you gain 2 life." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — At the beginning of combat on your turn, if you control a creature with power 4 or greater, put a +1/+1 counter on this creature." ==
  some [.ability (.triggered
    (.combatStart (.controller .this))
    (.if
      (.any (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this),
        .powerAtLeast (Value.int 4)]))
      [.putCounter (.source .this) .plusOnePlusOne 1]))]
#guard parseOracleParts (name := "")
  "At the beginning of combat on your turn, if you control a creature with power 4 or greater, put a +1/+1 counter on this creature." ==
  parseOracleParts (name := "")
    "Ferocious — At the beginning of combat on your turn, if you control a creature with power 4 or greater, put a +1/+1 counter on this creature."
#guard parseOracleParts (name := "")
  "Ferocious — At the beginning of combat on your turn, put a +1/+1 counter on this creature." ==
  none
#guard parseOracleParts (name := "")
  "Choose one —\n• Creatures you control get +2/+1 until end of turn.\n• Destroy target artifact or enchantment. You gain 2 life." ==
  some [.actions [.chooseUniqueModes (.range 1 1) [
    .continuous
      [.addPower
        (.intersection [
          .permanent, .cardType .creature, .controlled (.controller .this)])
        (Value.int 2),
       .addToughness
        (.intersection [
          .permanent, .cardType .creature, .controlled (.controller .this)])
        (Value.int 1)]
      .endOfTurn,
    .sequence [
      .destroy
        (.target 1
          (.intersection [
            .permanent,
            .union [.cardType .artifact, .cardType .enchantment]])),
      .gainLife (.controller .this) 2]]]]
#guard parseOracleParts (name := "")
  "Choose one —\n• Destroy target creature with power 4 or greater.\n• Until end of turn, target creature becomes an artifact in addition to its other types and gains indestructible. (Damage and effects that say \"destroy\" don't destroy it.)" ==
  some [.actions [.chooseUniqueModes (.range 1 1) [
    .destroy
      (.target 1
        (.intersection [
          .permanent, .cardType .creature, .powerAtLeast (Value.int 4)])),
    .continuous
      [.gainType
        (.target 2 (.intersection [.permanent, .cardType .creature]))
        .artifact,
       .gainAbility (.targetReference 2) (.keyword .indestructible)]
      .endOfTurn]]]
#guard parseOracleParts (name := "")
  "Until end of turn, target artifact becomes an artifact in addition to its other types and gains indestructible." ==
  none
#guard parseOracleParts (name := "") "This creature can't be blocked by tokens." ==
  some [.ability (.static (.forbid (.block .token .this)))]
#guard parseOracleParts (name := "Duskwatch Hunter")
  "Duskwatch Hunter can't be blocked by tokens." ==
  parseOracleParts (name := "") "This creature can't be blocked by tokens."
#guard parseOracleParts (name := "") "This creature can't be blocked by Goblins." == none
#guard parseOracleParts (name := "")
  "When this creature enters, put a +1/+1 counter on target creature." ==
  some [.ability (.triggered (.enter .this)
    (.putCounter
      (.target 1 (.intersection [.permanent, .cardType .creature]))
      .plusOnePlusOne
      1))]
#guard parseOracleParts (name := "")
  "When this creature enters, put a +1/+1 counter on target Elf." ==
  some [.ability
     (.triggered
       (.enter .this)
       (.putCounter
         (.target
           1
           (.intersection
             [.permanent,
              .cardType .creature,
              .subtype .elf]))
         .plusOnePlusOne
         1))]
#guard parseOracleParts (name := "")
  "When this creature enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)" ==
  some [.ability (.triggered (.enter .this) (.keyword (.controller .this) .recruit))]
#guard parseOracleParts (name := "Patient Instructor")
  "When Patient Instructor enters, recruit." ==
  parseOracleParts (name := "") "When this creature enters, recruit."
#guard parseOracleParts (name := "Gandalf") "When Patient Instructor enters, recruit." == none
#guard parseOracleParts (name := "")
  "Vigilance\nWhen this creature enters, recruit." ==
  some [
    .ability (.keyword .vigilance),
    .ability (.triggered (.enter .this) (.keyword (.controller .this) .recruit))]
#guard parseOracleParts (name := "")
  "Flying\nWhen this creature enters, recruit." ==
  some [
    .ability (.keyword .flying),
    .ability (.triggered (.enter .this) (.keyword (.controller .this) .recruit))]
#guard parseOracleParts (name := "")
  "When this creature dies, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)" ==
  some [.ability (.triggered (.die .this) (.keyword (.controller .this) .recruit))]
#guard parseOracleParts (name := "Lake-town Lookout")
  "When Lake-town Lookout dies, recruit." ==
  parseOracleParts (name := "") "When this creature dies, recruit."
#guard parseOracleParts (name := "Gandalf") "When Lake-town Lookout dies, recruit." == none
#guard parseOracleParts (name := "") "When this creature dies, draw a card." ==
  some [.ability
     (.triggered
       (.die .this)
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "") "When another creature dies, recruit." == none
#guard parseOracleParts (name := "")
  "When this artifact enters, scry 2. (Look at the top two cards of your library, then put any number of them on the bottom and the rest on top in any order.)" ==
  some [.ability (.triggered (.enter .this) (.scry (.controller .this) 2))]
#guard parseOracleParts (name := "") "When this creature enters, scry 0." == none
#guard parseOracleParts (name := "") "When this artifact enters, scry two." ==
  some [.ability (.triggered (.enter .this) (.scry (.controller .this) 2))]
#guard parseOracleParts (name := "")
  "{1}, {T}: Add one mana of any color." ==
  some [.ability (
    .activated
      [.mana [.generic 1], .tapSymbol]
      (.addManaOfOneColor (.controller .this) ManaSymbol.anyColor 1))]
#guard parseOracleParts (name := "") "Add one mana of any color." ==
  some [.actions
     [.addManaOfOneColor
        (.controller .this)
        [.colored .white,
         .colored .blue,
         .colored .black,
         .colored .red,
         .colored .green]
        (.nat 1)]]
#guard parseOracleParts (name := "") "{T}: Add one mana of any color." ==
  some [.ability
     (.activated
       [.tapSymbol]
       (.addManaOfOneColor
         (.controller .this)
         [.colored .white,
          .colored .blue,
          .colored .black,
          .colored .red,
          .colored .green]
         (.nat 1)))]
#guard parseOracleParts (name := "Giant's Boulder")
  "{7}, {T}, Sacrifice this artifact: Destroy target permanent." ==
  some [.ability (
    .activated
      [.mana [.generic 7], .tapSymbol, .sacrifice .this]
      (.destroy (.target 1 .permanent)))]
#guard parseOracleParts (name := "Giant's Boulder")
  "{7}, {T}, Sacrifice Giant's Boulder: Destroy target permanent." ==
  parseOracleParts (name := "Giant's Boulder")
    "{7}, {T}, Sacrifice this artifact: Destroy target permanent."
#guard parseOracleParts (name := "") "Destroy target permanent." ==
  some [.actions
     [.destroy (.target 1 .permanent)]]
#guard parseOracleParts (name := "")
  "When this creature enters, create a tapped Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")" ==
  some [.ability (
    .triggered
      (.enter .this)
      (.createTokens (.controller .this) 1 PredefinedToken.treasureToken [.tapped]))]
#guard parseOracleParts (name := "Dori, Bearer of Friends")
  "When Dori enters, create a Treasure token." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.createTokens (.controller .this) 1 PredefinedToken.treasureToken))]
#guard parseOracleParts (name := "Gandalf")
  "When Dori enters, create a Treasure token." == none
#guard parseOracleParts (name := "")
  "When this creature enters, create two Treasure tokens." ==
  some [.ability
     (.triggered
       (.enter .this)
       (.createTokens
         (.controller .this)
         (.nat 2)
         [.type .artifact,
          .subtype .treasure,
          .ability
            (.activated
              [.tapSymbol, .sacrifice .this]
              (.addManaOfOneColor
                (.controller .this)
                [.colored .white,
                 .colored .blue,
                 .colored .black,
                 .colored .red,
                 .colored .green]
                (.nat 1)))]
         []))]
#guard parseOracleParts (name := "")
  "When this creature enters, create a tapped Food token." == none
#guard parseOracleParts (name := "Esgaroth Garrison")
  "Esgaroth Garrison's power is equal to the number of creatures you control." ==
  some [.ability (
    .static
      (.setPower
        .this
        (.count
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]))))]
#guard parseOracleParts (name := "")
  "This creature's power is equal to the number of creatures you control." ==
  parseOracleParts (name := "Esgaroth Garrison")
    "Esgaroth Garrison's power is equal to the number of creatures you control."
#guard parseOracleParts (name := "Gandalf")
  "Esgaroth Garrison's power is equal to the number of creatures you control." == none
#guard parseOracleParts (name := "")
  "This creature's toughness is equal to the number of creatures you control." == none
#guard parseOracleParts (name := "")
  "When this creature enters, exile the top card of your library. Until the end of your next turn, you may play that card." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.sequence [
        .actionId 1 (.exile (.topOfLibrary (.controller .this) 1)),
        .continuous
          [.canPlay (.controller .this) (.wasCreatedByAction 1)]
          (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])]))]
#guard parseOracleParts (name := "")
  "When this creature enters, exile the top card of your library." == none
#guard parseOracleParts (name := "")
  "When this creature enters, exile the top card of your library. You may play it until the end of your next turn." == none
#guard parseOracleParts (name := "") "This spell can't be countered." ==
  some [.ability (.stackStatic (.forbid (.counter .this)))]
#guard parseOracleParts (name := "")
  "This spell can't be countered. (It can't be countered.)" ==
  parseOracleParts (name := "") "This spell can't be countered."
#guard parseOracleParts (name := "") "This creature can't be countered." == none
#guard parseOracleParts (name := "") "Hexproof, haste" ==
  some [.ability (.keyword .hexproof), .ability (.keyword .haste)]
#guard parseOracleParts (name := "")
  "Whenever you cast a noncreature spell, amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)" ==
  some [.ability (
    .triggered
      (.castSpell
        (.intersection [
          .spell,
          .not (.cardType .creature),
          .controlled (.controller .this)]))
      (.keyword (.controller .this) (.amass .goblin (.nat 1))))]
#guard parseOracleParts (name := "")
  "Whenever you cast a creature spell, amass Goblins 1." ==
  some [.ability
     (.triggered
       (.castSpell
         (.intersection
           [.spell,
            .cardType .creature,
            .controlled (.controller .this)]))
       (.keyword
         (.controller .this)
         (.amass .goblin (.nat 1))))]
#guard parseOracleParts (name := "") "Whenever you cast a noncreature spell, amass Goblin 1." == none
#guard parseOracleParts (name := "") "Whenever you cast a noncreature spell, amass Goblins 0." == none
#guard parseOracleParts (name := "")
  "When this creature enters, amass Goblins 1." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.keyword (.controller .this) (.amass .goblin (.nat 1))))]
#guard parseOracleParts (name := "Goblin-town Flunkies")
  "When Goblin-town Flunkies enters, amass Goblins 1." ==
  parseOracleParts (name := "") "When this creature enters, amass Goblins 1."
#guard parseOracleParts (name := "Gandalf")
  "When Goblin-town Flunkies enters, amass Goblins 1." == none
#guard parseOracleParts (name := "")
  "When this creature dies, amass Goblins 4." ==
  some [.ability (
    .triggered
      (.die .this)
      (.keyword (.controller .this) (.amass .goblin (.nat 4))))]
#guard parseOracleParts (name := "")
  "Whenever you attack, amass Goblins 2." ==
  some [.ability (
    .triggered
      (.attackSimultaneously
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])
        .all
        [])
      (.keyword (.controller .this) (.amass .goblin (.nat 2))))]
#guard parseOracleParts (name := "")
  "Whenever you attack while you control a Goblin, amass Goblins 2." == none
#guard parseOracleParts (name := "")
  "You may cast this spell as though it had flash if you control a Human." ==
  some [.ability (.everywhereStatic (
    .canBeCastAsThoughWithFlashIf
      .this
      (.any (.intersection [
        .permanent, .subtype .human, .controlled .caster]))))]
#guard parseOracleParts (name := "")
  "You may cast this spell as though it had flash if you control Human." == none
#guard parseOracleParts (name := "")
  "You may cast this spell as though it had flash if you control an Elf." ==
  some [.ability (.everywhereStatic (
    .canBeCastAsThoughWithFlashIf
      .this
      (.any (.intersection [
        .permanent, .subtype .elf, .controlled .caster]))))]
#guard parseOracleParts (name := "") "Other creatures you control get +1/+1." ==
  some [
    .ability (.static (.addPower
      (.intersection [
        .not .this,
        .permanent,
        .cardType .creature,
        .controlled (.controller .this)]) (Value.int 1))),
    .ability (.static (.addToughness
      (.intersection [
        .not .this,
        .permanent,
        .cardType .creature,
        .controlled (.controller .this)]) (Value.int 1)))]
#guard parseOracleParts (name := "") "Other creatures you control get +0/+0." == none
#guard parseOracleParts (name := "")
  "Other creatures you control get +1/+1 until end of turn." ==
  some [.actions
     [.continuous
        [.addPower
           (.intersection
             [.not .this,
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)])
           (.int 1),
         .addToughness
           (.intersection
             [.not .this,
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)])
           (.int 1)]
        .endOfTurn]]
#guard parseOracleParts (name := "")
  "Whenever this creature enters or attacks, recruit." ==
  some [.ability (
    .triggered
      (.or (.enter .this) (.attack .this .all))
      (.keyword (.controller .this) .recruit))]
#guard parseOracleParts (name := "Bard's Company")
  "Whenever Bard's Company enters or attacks, recruit." ==
  parseOracleParts (name := "") "Whenever this creature enters or attacks, recruit."
#guard parseOracleParts (name := "Gandalf")
  "Whenever Bard's Company enters or attacks, recruit." == none
#guard parseOracleParts (name := "")
  "Whenever this creature enters or attacks, draw a card." ==
  some [.ability
     (.triggered
       (.or
         (.enter .this)
         (.attack .this .all))
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "") "You draw a card and lose 1 life." ==
  some [.actions [
    .sequence [
      .draw (.controller .this) 1,
      .loseLife (.controller .this) 1]]]
#guard parseOracleParts (name := "") "You draw two cards and lose 1 life." ==
  some [.actions
     [.draw (.controller .this) (.nat 2),
      .loseLife
        (.controller .this)
        (.nat 1)]]
#guard parseOracleParts (name := "") "You draw a card and lose 2 life." ==
  some [.actions
     [.draw (.controller .this) (.nat 1),
      .loseLife
        (.controller .this)
        (.nat 2)]]
#guard parseOracleParts (name := "") "Amass Goblins 2." ==
  some [.actions [.keyword (.controller .this) (.amass .goblin (.nat 2))]]
#guard parseOracleParts (name := "")
  "Amass Goblins 2. (Put two +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)" ==
  parseOracleParts (name := "") "Amass Goblins 2."
#guard parseOracleParts (name := "") "Amass Goblin 2." == none
#guard parseOracleParts (name := "") "Amass Goblins 0." == none
#guard parseOracleParts (name := "")
  "You draw a card and lose 1 life.\nAmass Goblins 2." ==
  some [.actions [
    .draw (.controller .this) 1,
    .loseLife (.controller .this) 1,
    .keyword (.controller .this) (.amass .goblin (.nat 2))]]
#guard parseOracleParts (name := "")
  "Return up to one target creature card from your graveyard to your hand." ==
  some [.actions [
    .returnToHand
      (.targets 1 (.range 0 1)
        (.intersection [
          .inGraveyard,
          .cardType .creature,
          .owner (.controller .this)]))]]
#guard parseOracleParts (name := "")
  "Return up to one target creature from your graveyard to your hand." == none
#guard parseOracleParts (name := "")
  "Return target creature card from your graveyard to your hand." ==
  some [.actions
     [.returnToHand
        (.target
          1
          (.intersection
            [.inGraveyard,
             .cardType .creature,
             .owner (.controller .this)]))]]
#guard parseOracleParts (name := "")
  "Return up to one target creature card from your graveyard to your hand.\nAmass Goblins 3." ==
  some [.actions [
    .returnToHand
      (.targets 1 (.range 0 1)
        (.intersection [
          .inGraveyard,
          .cardType .creature,
          .owner (.controller .this)])),
    .keyword (.controller .this) (.amass .goblin (.nat 3))]]
#guard parseOracleParts (name := "")
  "Counter target spell. If that spell's mana value was 2 or less, recruit." ==
  some [.actions [
    .defineValueVariable 1 (.greatestManaValue (.target 1 .spell)),
    .counter (.targetReference 1),
    .if (.lessOrEqual (.variable 1) 2)
      [.keyword (.controller .this) .recruit]]]
#guard parseOracleParts (name := "")
  "Counter target spell. If that spell's mana value was 2 or less, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)" ==
  parseOracleParts (name := "")
    "Counter target spell. If that spell's mana value was 2 or less, recruit."
#guard parseOracleParts (name := "")
  "Counter target spell. If that spell's mana value was 2 or less, draw a card." == none
#guard parseOracleParts (name := "")
  "Counter target spell. If that spell's mana value was 0 or less, recruit." == none
#guard parseOracleParts (name := "")
  "Counter target creature. If that spell's mana value was 2 or less, recruit." == none
#guard parseOracleParts (name := "")
  "Whenever an artifact you control enters, draw a card." ==
  some [.ability (.triggered
    (.enter (.intersection [
      .permanent, .cardType .artifact, .controlled (.controller .this)]))
    (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "")
  "Whenever an artifact you control enters, draw two cards." ==
  some [.ability
     (.triggered
       (.enter
         (.intersection
           [.permanent,
            .cardType .artifact,
            .controlled (.controller .this)]))
       (.draw (.controller .this) (.nat 2)))]
#guard parseOracleParts (name := "")
  "Whenever a creature you control enters, draw a card." ==
  some [.ability
     (.triggered
       (.enter
         (.intersection
           [.permanent,
            .cardType .creature,
            .controlled (.controller .this)]))
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "Chief Warg's Company")
  "This creature can't attack unless you control two or more other Wolves." ==
  some [.ability (.static (.if
    (.less
      (.count (.intersection [
        .not .this, .permanent, .subtype .wolf, .controlled (.controller .this)]))
      (Value.nat 2))
    [.forbid (.attack .this .all)]))]
#guard parseOracleParts (name := "Chief Warg's Company")
  "Chief Warg's Company can't attack unless you control two or more other Wolves." ==
  parseOracleParts (name := "Chief Warg's Company")
    "This creature can't attack unless you control two or more other Wolves."
#guard parseOracleParts (name := "Gandalf")
  "Chief Warg's Company can't attack unless you control two or more other Wolves." == none
#guard parseOracleParts (name := "")
  "This creature can't attack unless you control two or more other Wolf." == none
#guard parseOracleParts (name := "")
  "This creature can't attack unless you control two other Wolves." == none
#guard parseOracleParts (name := "")
  "At the beginning of your upkeep, create a 2/2 green Wolf creature token." ==
  some [.ability (.triggered
    (.upkeep (.controller .this))
    (.createTokens (.controller .this) 1 [
      .type .creature, .subtype .wolf, .colorIndicator [.green],
      .power 2, .toughness 2]))]
#guard parseOracleParts (name := "")
  "At the beginning of your upkeep, create two 2/2 green Wolf creature tokens." ==
  some [.ability (.triggered
    (.upkeep (.controller .this))
    (.createTokens (.controller .this) 2 [
      .type .creature, .subtype .wolf, .colorIndicator [.green],
      .power 2, .toughness 2]))]
#guard parseOracleParts (name := "")
  "At the beginning of your upkeep, create a 2/2 green Wolf creature tokens." == none
#guard parseOracleParts (name := "")
  "When this Equipment enters, create a 2/2 red Dwarf creature token, then attach this Equipment to it." ==
  some [.ability (.triggered
    (.enter .this)
    (.sequence [
      .actionId 1
        (.createTokens (.controller .this) 1 [
          .type .creature, .subtype .dwarf, .colorIndicator [.red],
          .power 2, .toughness 2]),
      .attach .this (.wasCreatedByAction 1)]))]
#guard parseOracleParts (name := "")
  "When this Equipment enters, create two 2/2 red Dwarf creature tokens, then attach this Equipment to it." ==
  none
#guard parseOracleParts (name := "")
  "When this Equipment enters, amass Goblins 1, then attach this Equipment to the amassed Army." ==
  some [.ability (.triggered
    (.enter .this)
    (.sequence [
      .actionId 1 (.keyword (.controller .this) (.amass .goblin (.nat 1))),
      .attach .this (.wasObjectOfAction 1)]))]
#guard parseOracleParts (name := "")
  "When this Equipment enters, amass Goblins 1, then attach this Equipment to the amassed Army. (To amass Goblins 1, put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)" ==
  parseOracleParts (name := "")
    "When this Equipment enters, amass Goblins 1, then attach this Equipment to the amassed Army."
#guard parseOracleParts (name := "")
  "Put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control." ==
  some [.actions [
    .putCounter
      (.target 1 (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this)]))
      .plusOnePlusOne 1,
    .if (.happened (.castSpellFromGraveyard .this) .gameStart)
      [.putCounter
        (.intersection [
          .not (.targetReference 1),
          .permanent, .cardType .creature, .controlled (.controller .this)])
        .plusOnePlusOne 1]]]
#guard parseOracleParts (name := "") "Flashback {4}{W}" ==
  some [.ability (.keywordWithCost .flashback [.mana [.generic 4, .mono .white]])]
#guard parseOracleParts (name := "")
  "Flashback {4}{W} (You may cast this card from your graveyard for its flashback cost. Then exile it.)" ==
  parseOracleParts (name := "") "Flashback {4}{W}"
#guard parseOracleParts (name := "") "Flashback" == none
#guard parseOracleParts (name := "") "Teamwork 2" ==
  some [.ability (.keyword (.teamwork 2))]
#guard parseOracleParts (name := "")
  "Teamwork 2 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 2 or more.)" ==
  parseOracleParts (name := "") "Teamwork 2"
#guard parseOracleParts (name := "") "Teamwork" == none
#guard parseOracleParts (name := "") "Teamwork 0" == none
#guard parseOracleParts (name := "") "Improvise" ==
  some [.ability (.keyword .improvise)]
#guard parseOracleParts (name := "")
  "Improvise (Your artifacts can help cast this spell. Each artifact you tap after you're done activating mana abilities pays for {1}.)" ==
  parseOracleParts (name := "") "Improvise"
#guard parseOracleParts (name := "") "Kicker {2}{W}" ==
  some [.ability (.keywordWithCost .kicker [.mana [.generic 2, .mono .white]])]
#guard parseOracleParts (name := "")
  "Kicker {2}{W}{W} (You may pay an additional {2}{W}{W} as you cast this spell.)" ==
  some [.ability (.keywordWithCost .kicker [.mana [.generic 2, .mono .white, .mono .white]])]
#guard parseOracleParts (name := "") "Kicker" == none
#guard parseOracleParts (name := "") "Affinity for Elves" ==
  some [.ability (.keyword (.affinity [] [.elf]))]
#guard parseOracleParts (name := "")
  "Affinity for Elves (This spell costs {1} less to cast for each Elf you control.)" ==
  parseOracleParts (name := "") "Affinity for Elves"
#guard parseOracleParts (name := "") "Affinity for artifacts" ==
  some [.ability (.keyword (.affinity [.artifact] []))]
#guard parseOracleParts (name := "") "Affinity for Elf" == none
#guard parseOracleParts (name := "") "Affinity" == none
#guard parseOracleParts (name := "") "Boast" ==
  some [.ability (.keyword .boast)]
#guard parseOracleParts (name := "") "Cascade, cascade" ==
  some [.ability (.keyword .cascade), .ability (.keyword .cascade)]
#guard parseOracleParts (name := "")
  "Cascade, cascade (When you cast this spell, exile cards from the top of your library until you exile a nonland card that costs less. You may cast it without paying its mana cost. Put the exiled cards on the bottom of your library in a random order. Then do it again.)" ==
  parseOracleParts (name := "") "Cascade, cascade"
#guard parseOracleParts (name := "") "Extort" ==
  some [.ability (.keyword .extort)]
#guard parseOracleParts (name := "") "Sneak {1}{B}{B}" ==
  some [.ability (.keywordWithCost .sneak [.mana [.generic 1, .mono .black, .mono .black]])]
#guard parseOracleParts (name := "")
  "Sneak {1}{B}{B} (You may cast this spell for {1}{B}{B} if you also return an unblocked attacker you control to hand during the declare blockers step. She enters tapped and attacking.)" ==
  parseOracleParts (name := "") "Sneak {1}{B}{B}"
#guard parseOracleParts (name := "") "Sneak" == none
#guard parseOracleParts (name := "") "Gift a Food" ==
  some [.ability (.keyword (.gift .food))]
#guard parseOracleParts (name := "")
  "Gift a Food (You may promise an opponent a gift as you cast this spell. If you do, they create a Food token before its other effects.)" ==
  parseOracleParts (name := "") "Gift a Food"
#guard parseOracleParts (name := "") "Gift a card" ==
  some [.ability (.keyword (.gift .card))]
#guard parseOracleParts (name := "") "Gift a tapped Fish" ==
  some [.ability (.keyword (.gift .tappedFish))]
#guard parseOracleParts (name := "") "Gift an extra turn" ==
  some [.ability (.keyword (.gift .extraTurn))]
#guard parseOracleParts (name := "") "Gift a Treasure" ==
  some [.ability (.keyword (.gift .treasure))]
#guard parseOracleParts (name := "")
  "Gift a Treasure (You may promise an opponent a gift as you cast this spell. If you do, they create a Treasure token before its other effects. It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")" ==
  parseOracleParts (name := "") "Gift a Treasure"
#guard parseOracleParts (name := "") "Gift an Octopus" ==
  some [.ability (.keyword (.gift .octopus))]
#guard parseOracleParts (name := "") "Gift" == none
#guard parseOracleParts (name := "")
  "Return target spell to its owner's hand. If the gift was promised, players can't cast spells this turn." ==
  some [.actions [
    .returnToHand (.target 1 .spell),
    .if (.happened (.giftPromised .this) .gameStart) [
      .continuous [.forbid (.castSpell .all)] .endOfTurn]]]
#guard parseOracleParts (name := "")
  "Draw a card. If this spell was cast from a graveyard, draw two cards instead." ==
  some [.actions [
    .ifElse (.happened (.castSpellFromGraveyard .this) .gameStart)
      [.draw (.controller .this) 2]
      [.draw (.controller .this) 1]]]
#guard parseOracleParts (name := "")
  "Amass Goblins 1. If this spell was cast from a graveyard, amass Goblins 3 instead." ==
  some [.actions [
    .ifElse (.happened (.castSpellFromGraveyard .this) .gameStart)
      [.keyword (.controller .this) (.amass .goblin 3)]
      [.keyword (.controller .this) (.amass .goblin 1)]]]
#guard parseOracleParts (name := "") "Draw a card." ==
  some [.actions
     [.draw (.controller .this) (.nat 1)]]
#guard parseOracleParts (name := "")
  "Draw a card. If this spell was cast from a graveyard, amass Goblins 3 instead." == none
#guard parseOracleParts (name := "")
  "Put two +1/+1 counters on target creature you control. Then it fights target creature an opponent controls." ==
  some [.actions [
    .putCounter
      (.target 1 (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this)]))
      .plusOnePlusOne 2,
    .fight (.targetReference 1)
      (.target 2 (.intersection [
        .permanent, .cardType .creature,
        .controlled (.opponent (.controller .this))]))]]
#guard parseOracleParts (name := "") "Enchant creature" ==
  some [.ability (.keywordWithTarget .enchant 1
    (.intersection [.permanent, .cardType .creature]))]
#guard parseOracleParts (name := "") "Ward {3}" ==
  some [.ability (.keywordWithCost .ward [.mana [.generic 3]])]
#guard parseOracleParts (name := "") "Ward {U}" == none
#guard parseOracleParts (name := "")
  "Enchanted creature gets +2/+2 and has flying." ==
  some [
    .ability (.static (.addPower (.hostOf .this) (Value.int 2))),
    .ability (.static (.addToughness (.hostOf .this) (Value.int 2))),
    .ability (.static (.gainAbility (.hostOf .this) (.keyword .flying)))]
#guard parseOracleParts (name := "")
  "Equipped creature gets +2/+2 and has ward {1}." ==
  some [
    .ability (.static (.addPower (.hostOf .this) (Value.int 2))),
    .ability (.static (.addToughness (.hostOf .this) (Value.int 2))),
    .ability (.static (.gainAbility (.hostOf .this)
      (.keywordWithCost .ward [.mana [.generic 1]])))]
#guard parseOracleParts (name := "Gandalf, Wandering Wizard")
  "{6}: Gandalf's owner shuffles him into their library and draws three cards." ==
  some [.ability (.activated [.mana [.generic 6]]
    (.sequence [
      .defineSelectorVariable 1 (.owner (.source .this)),
      .shuffleIntoOwnersLibrary (.source .this),
      .draw (.variable 1) 3]))]
#guard parseOracleParts (name := "")
  "{2}{W/U}{W/U}: Return this card from your graveyard to the battlefield attached to target creature you control with power 1 or less. Activate only as a sorcery." ==
  some [.ability (.graveyardActivatedIf
    (.timeToCastSorcery (.controller .this))
    [.mana [.generic 2, .hybrid .white .blue, .hybrid .white .blue]]
    (.putOntoBattlefieldInState
      (.intersection [.inGraveyard, .source .this])
      [.attachedTo
        (.target 1 (.intersection [
          .permanent, .cardType .creature, .controlled (.controller .this),
          .powerAtMost (Value.int 1)]))]))]
#guard parseOracleParts (name := "")
  "When this Equipment enters, attach it to target Dwarf you control." ==
  some [.ability (.triggered (.enter .this)
    (.attach .this
      (.target 1 (.intersection [
        .permanent, .cardType .creature, .subtype .dwarf,
        .controlled (.controller .this)]))))]
#guard parseOracleParts (name := "")
  "Each creature you control with a +1/+1 counter on it has menace." ==
  some [.ability (.static (.gainAbility
    (.intersection [
      .permanent, .cardType .creature, .controlled (.controller .this),
      .hasCounter .plusOnePlusOne])
    (.keyword .menace)))]
#guard parseOracleParts (name := "")
  "At the beginning of your end step, draw a card." ==
  some [.ability (.triggered (.endStep (.controller .this))
    (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "")
  "At the beginning of your end step, draw two cards." ==
  some [.ability (.triggered (.endStep (.controller .this))
    (.draw (.controller .this) 2))]
#guard parseOracleParts (name := "")
  "At the beginning of your end step, draw two." == none
#guard parseOracleParts (name := "")
  "Search your library for a legendary creature card, reveal it, put it into your hand, then shuffle." ==
  some [.actions [
    .searchLibraryThenShuffle (.controller .this) [
      .defineSelectorVariable 1
        (.selected (.controller .this) (.range 1 1)
          (.intersection [
            .inLibrary, .cardType .creature, .supertype .legendary])),
      .reveal (.variable 1),
      .returnToHand (.variable 1)]]]
#guard parseOracleParts (name := "") "Creatures you control get +1/+1." ==
  some [
    .ability (.static (.addPower
      (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this)])
      (Value.int 1))),
    .ability (.static (.addToughness
      (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this)])
      (Value.int 1)))]
#guard parseOracleParts (name := "")
  "This creature has haste as long as you control another Goblin." ==
  some [.ability (.static (.if
    (.any (.intersection [
      .not .this, .permanent, .subtype .goblin,
      .controlled (.controller .this)]))
    [.gainAbility .this (.keyword .haste)]))]
#guard parseOracleParts (name := "Bolg's Company")
  "{T}, Sacrifice another Goblin: Add {B}{R}." ==
  some [.ability (.activated
    [.tapSymbol,
      .sacrificeCount
        (.intersection [
          .not .this, .permanent, .subtype .goblin,
          .controlled (.controller .this)])
        1]
    (.addMana (.controller .this) [.colored .black, .colored .red]))]
#guard parseOracleParts (name := "") "{T}: Add {G}." ==
  some [.ability
     (.activated
       [.tapSymbol]
       (.addMana
         (.controller .this)
         [.colored .green]))]
#guard parseOracleParts (name := "") "{T}, Sacrifice another: Add {B}{R}." == none
#guard parseOracleParts (name := "Nori, Teller of Tales")
  "Whenever Nori attacks, target attacking creature gains first strike until end of turn." ==
  some [.ability (.triggered (.attack .this .all)
    (.continuous
      [.gainAbility
        (.target 1 (.intersection [
          .permanent, .cardType .creature, .attacking .all]))
        (.keyword .firstStrike)]
      .endOfTurn))]
#guard parseOracleParts (name := "Gandalf")
  "Whenever Nori attacks, target attacking creature gains first strike until end of turn." ==
  none
#guard parseOracleParts (name := "")
  "This spell costs {X} less to cast, where X is the total power of creatures you control with flying." ==
  some [.ability (.stackStatic
    (.reduceCostWithX .this [.mana [.x]]
      (.totalPower (.intersection [
        .permanent, .cardType .creature, .keyword .flying,
        .controlled (.controller .this)]))))]
#guard parseOracleParts (name := "")
  "This spell costs {2} less to cast, where X is the total power of creatures you control with flying." ==
  none
#guard parseOracleParts (name := "Thrór's Map")
  "When Thrór's Map enters, search your library for a basic land card, reveal it, put it into your hand, then shuffle." ==
  some [.ability (.triggered (.enter .this)
    (.searchLibraryThenShuffle (.controller .this) [
      .defineSelectorVariable 1
        (.selected (.controller .this) (.range 1 1)
          (.intersection [.inLibrary, .cardType .land, .supertype .basic])),
      .reveal (.variable 1),
      .returnToHand (.variable 1)]))]
#guard parseOracleParts (name := "")
  "{2}, {T}: Draw a card, then discard a card." ==
  some [.ability (.activated
    [.mana [.generic 2], .tapSymbol]
    (.sequence [
      .draw (.controller .this) 1,
      .discard (.controller .this) 1]))]
#guard parseOracleParts (name := "The Black Arrow")
  "When The Black Arrow enters, it deals 1 damage to any target. If a Dragon is dealt damage this way, destroy it." ==
  some [.ability (.triggered (.enter .this)
    (.sequence [
      .actionId 1
        (.dealDamage (.source .this) (.target 1 .all) 1),
      .if (.anySubtype (.wasObjectOfAction 1) .dragon)
        [.destroy (.wasObjectOfAction 1)]]))]
#guard parseOracleParts (name := "Gandalf")
  "When The Black Arrow enters, it deals 1 damage to any target. If a Dragon is dealt damage this way, destroy it." ==
  none
#guard parseOracleParts (name := "Smaug the Magnificent")
  "Whenever Smaug attacks, he deals damage equal to the number of Treasures you control to any target." ==
  some [.ability (.triggered (.attack .this .all)
    (.dealDamage (.source .this) (.target 1 .all)
      (.count (.intersection [
        .permanent, .cardType .artifact, .subtype .treasure,
        .controlled (.controller .this)]))))]
#guard parseOracleParts (name := "")
  "At the beginning of your upkeep, create a Treasure token." ==
  some [.ability (.triggered (.upkeep (.controller .this))
    (.createTokens (.controller .this) 1 PredefinedToken.treasureToken))]
#guard parseOracleParts (name := "")
  "Whenever an opponent casts their first noncreature spell each turn, you recruit." ==
  some [.ability (.triggered
    (.ordinal 1 .turnStart
      (.castSpell (.intersection [
        .spell, .not (.cardType .creature),
        .controlled (.opponent (.controller .this))])))
    (.keyword (.controller .this) .recruit))]
#guard parseOracleParts (name := "Ori, Keeper of Songs")
  "As long as you have an enduring story, Ori gets +1/+0 and has vigilance." ==
  some [.ability (.static (.if (.enduringStory (.controller .this))
    [.addPower .this (Value.int 1), .gainAbility .this (.keyword .vigilance)]))]
#guard parseOracleParts (name := "Gandalf")
  "As long as you have an enduring story, Ori gets +1/+0 and has vigilance." == none
#guard parseOracleParts (name := "Ori, Keeper of Songs")
  "As long as you have an enduring story, Ori gets +0/+0." == none
#guard parseOracleParts (name := "Óin the Brave")
  "As long as you have an enduring story, Óin gets +1/+0 and has haste." ==
  some [.ability (.static (.if (.enduringStory (.controller .this))
    [.addPower .this (Value.int 1), .gainAbility .this (.keyword .haste)]))]
#guard parseOracleParts (name := "Óin the Brave")
  "{1}, {T}, Discard a card: Draw a card." ==
  some [.ability (.activated
    [.mana [.generic 1], .tapSymbol,
      .discard
        (.selected
          (.controller .this)
          (.range 1 1)
          (.intersection [.inHand, .owner (.controller .this)]))]
    (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "Óin the Brave")
  "{1}, {T}: Draw a card." ==
  some [.ability
     (.activated
       [.mana [.generic 1], .tapSymbol]
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "Fíli the Pathfinder")
  "As long as you have an enduring story, creatures you control get +1/+1." ==
  some [.ability (.static (.if (.enduringStory (.controller .this))
    [.addPower creaturesYouControl (Value.int 1),
      .addToughness creaturesYouControl (Value.int 1)]))]
#guard parseOracleParts (name := "Fíli the Pathfinder")
  "As long as you have an enduring story, creatures you control get +0/+0." == none
#guard parseOracleParts (name := "Thorin Oakenshield")
  "As long as you have an enduring story, artifacts and creatures you control have ward {1}." ==
  some [.ability (.static (.if (.enduringStory (.controller .this))
    [.gainAbility
      (permanentWith [.artifact, .creature] [youControl])
      (.keywordWithCost .ward [.mana [.generic 1]])]))]
#guard parseOracleParts (name := "Thorin Oakenshield")
  "As long as you have an enduring story, artifacts and creatures you control have ward {0}." ==
  none
#guard parseOracleParts (name := "Dáin, Lord of the Iron Hills")
  "As long as you have an enduring story, creatures can't attack you unless their controller pays {1} for each of those creatures." ==
  some [.ability (.static (.if (.enduringStory (.controller .this))
    [.cantAttackUnlessPays
      (permanentWith [.creature])
      (.controller .this)
      [.mana [.generic 1]]]))]
#guard parseOracleParts (name := "Bombur, Gentle Dreamer")
  "Bombur doesn't untap during your untap step unless you have an enduring story." ==
  some [.ability (.static
    (.if (.not (.enduringStory (.controller .this)))
      [.doesntUntap .this]))]
#guard parseOracleParts (name := "Gandalf")
  "Bombur doesn't untap during your untap step unless you have an enduring story." == none
#guard parseOracleParts (name := "Fíli the Pathfinder")
  "Whenever Fíli or another nontoken Dwarf you control enters, create a 2/2 red Dwarf creature token." ==
  some [.ability (.triggered
    (.or
      (.enter .this)
      (.enter
        (.intersection [
          .not .this,
          .not .token,
          .permanent,
          .cardType .creature,
          .subtype .dwarf,
          youControl])))
    (.createTokens (.controller .this) 1 [
      .type .creature,
      .subtype .dwarf,
      .colorIndicator [.red],
      .power 2,
      .toughness 2]))]
#guard parseOracleParts (name := "Gandalf")
  "Whenever Fíli or another nontoken Dwarf you control enters, create a 2/2 red Dwarf creature token." ==
  none
#guard parseOracleParts (name := "Old Thrush")
  "When this creature enters, you gain 2 life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top." ==
  some [.ability (.triggered (.enter .this)
    (.sequence [
      .gainLife (.controller .this) 2,
      .optional (.controller .this)
        (.sequence [
          .searchLibraryThenShuffle (.controller .this) [
            .defineSelectorVariable 1
              (.selected (.controller .this) (.range 1 1)
                (.intersection [.inLibrary, .cardType .land, .supertype .basic])),
            .reveal (.variable 1),
            .holdOutInLibrary (.variable 1)],
          .putOnTopOfLibrary (.variable 1)])]))]
#guard parseOracleParts (name := "Old Thrush")
  "When this creature enters, you gain 2 life." ==
  some [.ability (.triggered (.enter .this) (.gainLife (.controller .this) 2))]
#guard parseOracleParts (name := "Old Thrush")
  "When this creature enters, you gain 2 life. Draw a card." ==
  some [.ability
     (.triggered
       (.enter .this)
       (.sequence
         [.gainLife
            (.controller .this)
            (.nat 2),
          .draw
            (.controller .this)
            (.nat 1)]))]
#guard parseOracleParts (name := "Gandalf")
  "When Old Thrush enters, you gain 2 life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top." ==
  none
#guard parseOracleParts (name := "Most Decrepit Old Bird")
  "Threshold — This creature gets +1/+1 as long as there are seven or more cards in your graveyard." ==
  some [.ability (.static (.if
    (.greaterOrEqual
      (.count (.intersection [.inGraveyard, .owner (.controller .this)]))
      7)
    [.addPower .this (Value.int 1), .addToughness .this (Value.int 1)]))]
#guard parseOracleParts (name := "Most Decrepit Old Bird")
  "This creature gets +1/+1 as long as there are seven or more cards in your graveyard." ==
  parseOracleParts (name := "Most Decrepit Old Bird")
    "Threshold — This creature gets +1/+1 as long as there are seven or more cards in your graveyard."
#guard parseOracleParts (name := "Most Decrepit Old Bird")
  "Threshold — This creature gets +0/+0 as long as there are seven or more cards in your graveyard." ==
  none
#guard parseOracleParts (name := "Most Decrepit Old Bird")
  "Threshold — This creature gets +1/+1 as long as there are six or more cards in your graveyard." ==
  none
#guard parseOracleParts (name := "Gandalf")
  "Threshold — Most Decrepit Old Bird gets +1/+1 as long as there are seven or more cards in your graveyard." ==
  none
#guard parseOracleParts (name := "")
  "Mill four cards, then put an instant or sorcery card from among them into your hand." ==
  some [.actions [.sequence [
    .actionId 1 (.mill (.controller .this) 4),
    .returnToHand
      (.selected (.controller .this) (.range 1 1)
        (.intersection [
          .wasObjectOfAction 1,
          .union [.cardType .instant, .cardType .sorcery]]))]]]
#guard parseOracleParts (name := "")
  "Mill one cards, then put an instant or sorcery card from among them into your hand." == none
#guard parseOracleParts (name := "")
  "Mill four cards, then put a creature card from among them into your hand." == none
#guard parseOracleParts (name := "")
  "Exile two target creatures and/or lands you control, then return them to the battlefield under their owner's control." ==
  some [.actions [.sequence [
    .actionId 1 (.exile (.targets 1 (.range 2 2)
      (.intersection [
        .permanent,
        .union [.cardType .creature, .cardType .land],
        .controlled (.controller .this)]))),
    .putOntoBattlefieldInState (.wasCreatedByAction 1)
      [.controlled (.owner (.wasCreatedByAction 1))]]]]
#guard parseOracleParts (name := "")
  "Exile one target creatures and/or lands you control, then return them to the battlefield under their owner's control." ==
  none
#guard parseOracleParts (name := "Pinecone Strike")
  "Choose one or both —\n• Pinecone Strike deals 3 damage to target creature. If that creature would die this turn, exile it instead.\n• Destroy target artifact token." ==
  some [.actions [.chooseUniqueModes (.range 1 2) [
    .sequence [
      .dealDamage .this
        (.target 1 (.intersection [.permanent, .cardType .creature])) 3,
      .continuous
        [.replace (.putToGraveyard (.targetReference 1)) [.exile .replacingObject]]
        .endOfTurn],
    .destroy (.target 2 artifactTokenPermanent)]]]
#guard parseOracleParts (name := "Other")
  "Pinecone Strike deals 3 damage to target creature. If that creature would die this turn, exile it instead." ==
  none
#guard parseOracleParts (name := "")
  "Mill four cards, then put up to two land cards from among them into your hand." ==
  some [.actions [.sequence [
    .actionId 1 (.mill (.controller .this) 4),
    .returnToHand
      (.selected (.controller .this) (.range 0 2)
        (.intersection [.wasObjectOfAction 1, .cardType .land]))]]]
#guard parseOracleParts (name := "")
  "Mill one cards, then put up to two land cards from among them into your hand." == none
#guard parseOracleParts (name := "Easy Pickings")
  "Easy Pickings deals 1 damage to each creature your opponents control." ==
  some [.actions [.dealDamage .this eachOppCreature 1]]
#guard parseOracleParts (name := "Desolation of Smaug")
  "Desolation of Smaug deals 3 damage to each non-Dragon creature.\nAdd four mana in any combination of colors. Spend this mana only to cast Dragon spells." ==
  some [.actions [
    .dealDamage .this eachNonDragonCreature 3,
    .actionId 1 (.addManaInAnyCombination
      (.controller .this) ManaSymbol.anyColor 4),
    .continuous
      [.forbid (.spendManaCreatedByAction 1 (.not (.castSpell (.subtype .dragon))))]
      .endOfTurn]]
#guard parseOracleParts (name := "Thranduil, Sindarin Liege")
  "Other Elves you control get +1/+1." ==
  some [
    .ability (.static (.addPower
      (.intersection [
        .not .this, .permanent, .cardType .creature, .subtype .elf, youControl])
      (Value.int 1))),
    .ability (.static (.addToughness
      (.intersection [
        .not .this, .permanent, .cardType .creature, .subtype .elf, youControl])
      (Value.int 1)))]
#guard parseOracleParts (name := "The Lonely Mountain")
  "({T}: Add {R}.)\nThis land enters tapped unless you control an Equipment." ==
  some [.ability (.everywhereStatic (.if (.not (.any equipmentYouControl))
    [.replace (.enter .this) [.putOntoBattlefieldInState .this [.tapped]]]))]
#guard parseOracleParts (name := "Glóin the Mighty")
  "At the beginning of your first main phase, add {R}{R}." ==
  some [.ability (.triggered (.precombatMainPhase (.controller .this))
    (.addMana (.controller .this) [.colored .red, .colored .red]))]
#guard parseOracleParts (name := "Iron Hills Stalwart")
  "When this creature enters, attach target Equipment you control to up to one target creature you control." ==
  some [.ability (.triggered (.enter .this)
    (.attach
      (.target 1 equipmentYouControl)
      (.targets 2 (.range 0 1) creaturesYouControl)))]
#guard parseOracleParts (name := "Old Fat Spider")
  "This creature can't be blocked by creatures with power 2 or less.\nWhenever this creature becomes the target of a spell or ability an opponent controls, draw a card." ==
  some [
    .ability (.static (.forbid (.block
      (.intersection [.permanent, .cardType .creature, .powerAtMost (Value.int 2)])
      .this))),
    .ability (.triggered
      (.target spellOrAbilityOpponentControls .this)
      (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "Great Gilded Boat")
  "Whenever you attack, recruit.\nCrew 2" ==
  some [
    .ability (.triggered
      (.attackSimultaneously creaturesYouControl .all [])
      (.keyword (.controller .this) .recruit)),
    .ability (.keyword (.crew 2))]
#guard parseOracleParts (name := "") "Crew 0" == none
#guard parseOracleParts (name := "Dwarven Mauler")
  "Equip abilities you activate that target this creature cost {2} less to activate." ==
  some [.ability (.static (.reduceCost
    (.intersection [
      Selector.keywordAbility .equip,
      .hasTarget .this,
      .controlled (.controller .this)])
    [.mana [.generic 2]]))]
#guard parseOracleParts (name := "")
  "Equip abilities you activate that target this creature cost {0} less to activate." ==
  none
#guard parseOracleParts (name := "My Precious")
  "Equipped creature has hexproof and can't be blocked.\nEquip—{2}, Pay 2 life." ==
  some [
    .ability (.static (.gainAbility (.hostOf .this) (.keyword .hexproof))),
    .ability (.static (.forbid (.block .any (.hostOf .this)))),
    .ability (.keywordWithCost .equip [.mana [.generic 2], .life 2])]
#guard parseOracleParts (name := "My Precious")
  "Equipped creature has hexproof and can't be blocked.\nEquip—{2}, Pay 2 life.\n//ADV//\nAllure of Power {1}{B}\nInstant — Adventure\nAs an additional cost to cast this spell, sacrifice a creature.\nDraw two cards. (Then exile this card. You may cast the artifact later from exile.)" ==
  some [
    .ability (.static (.gainAbility (.hostOf .this) (.keyword .hexproof))),
    .ability (.static (.forbid (.block .any (.hostOf .this)))),
    .ability (.keywordWithCost .equip [.mana [.generic 2], .life 2]),
    .alternative [
      .name "Allure of Power",
      .manaCost [.generic 1, .mono .black],
      .type .instant,
      .subtype .adventure,
      .ability (.stackStatic (.additionalCost .this
        [.sacrificeCount (permanentWith [.creature]) 1])),
      .actions [.draw (.controller .this) 2]]]
#guard parseOracleParts (name := "")
  "Flying\n//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure\nDraw two cards." == none
#guard parseOracleParts (name := "Troop of Ponies")
  "{2}, {T}, Sacrifice this creature: Search your library for up to two basic land cards, reveal them, put one onto the battlefield tapped and the other into your hand, then shuffle." ==
  some [.ability (.activated
    [.mana [.generic 2], .tapSymbol, .sacrifice .this]
    (.searchLibraryThenShuffle
      (.controller .this)
      [
        .defineSelectorVariable 1
          (.selected
            (.controller .this)
            (.range 0 2)
            (.intersection [
              .inLibrary, .cardType .land, .supertype .basic])),
        .reveal (.variable 1),
        .putOntoBattlefieldInState
          (.selected (.controller .this) (.range 1 1) (.variable 1))
          [.tapped],
        .returnToHand (.variable 1)]))]
#guard parseOracleParts (name := "")
  "{2}, {T}, Sacrifice this creature: Search your library for up to one basic land card, reveal it, put it onto the battlefield tapped, then shuffle." ==
  none
#guard parseOracleParts (name := "Elven Raft-Steerer")
  "Landfall — Whenever a land you control enters, choose one —\n• Tap target creature an opponent controls.\n• Untap target creature you control." ==
  some [.ability (.triggered
    (.enter landsYouControl)
    (.chooseUniqueModes (.range 1 1) [
      .tap (.target 1 (permanentWith [.creature]
        [.controlled (.opponent (.controller .this))])),
      .untap (.target 2 (permanentWith [.creature] [youControl]))]))]
#guard parseOracleParts (name := "")
  "Landfall — Whenever a land you control enters, choose one —" == none
#guard parseOracleParts (name := "Mirkwood Meditator")
  "Landfall — Whenever a land you control enters, you may have this creature's base power and toughness become 4/2 until end of turn." ==
  some [.ability (.triggered
    (.enter landsYouControl)
    (.optional (.controller .this) (.continuous
      [.setBasePower (.source .this) (Value.int 4),
        .setBaseToughness (.source .this) (Value.int 2)]
      .endOfTurn)))]
#guard parseOracleParts (name := "Mirkwood Nurturer")
  "When this creature enters, return up to one other target permanent you control to its owner's hand. If you do, put a +1/+1 counter on this creature." ==
  some [.ability (.triggered
    (.enter .this)
    (.sequence [
      .actionId 1
        (.returnToHand
          (.targets 1 (.range 0 1)
            (.intersection [.not .this, .permanent, youControl]))),
      .if (.happened (.actionWithId 1) .gameStart)
        [.putCounter (.source .this) .plusOnePlusOne 1]]))]
#guard parseOracleParts (name := "Kíli the Resourceful")
  "As long as you have an enduring story, you may pay {0} rather than pay the equip cost of the first equip ability you activate each turn.\nWhenever another Dwarf or Equipment you control enters, draw a card. This ability triggers only once each turn." ==
  some [
    .ability (.static (.if
      (.and
        (.enduringStory (.controller .this))
        (.didNotHappen
          (.activateAbility
            (.intersection [
              Selector.keywordAbility .equip,
              .controlled (.controller .this)]))
          .turnStart))
      [.alternativeCost
        (.intersection [
          Selector.keywordAbility .equip,
          .controlled (.controller .this)])
        [.mana [.generic 0]]])),
    .ability (.triggered
      (.enter (.intersection [
        .not .this,
        .permanent,
        .union [.subtype .dwarf, .subtype .equipment],
        youControl]))
      (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "")
  "As long as you have an enduring story, you may pay {1} rather than pay the equip cost of the first equip ability you activate each turn." ==
  none
#guard parseOracleParts (name := "")
  "Whenever another Dwarf or Equipment you control enters, draw a card." ==
  some [.ability
     (.triggered
       (.enter
         (.intersection
           [.not .this,
            .permanent,
            .union
              [.subtype .dwarf,
               .subtype .equipment],
            .controlled (.controller .this)]))
       (.draw (.controller .this) (.nat 1)))]
#guard parseOracleParts (name := "Dáin's Company")
  "This creature has lifelink as long as you control another Dwarf.\nWhen this creature enters, look at the top four cards of your library. You may reveal a Dwarf or Equipment card from among them and put it into your hand. Put the rest on the bottom of your library in a random order." ==
  some [
    .ability (.static (.if
      (.any (.intersection [.not .this, .permanent, .subtype .dwarf, youControl]))
      [.gainAbility .this (.keyword .lifelink)])),
    .ability (.triggered (.enter .this) (.sequence [
      .actionId 1
        (.lookAt (.topOfLibrary (.controller .this) 4)),
      .optional (.controller .this) (.sequence [
        .actionId 2
          (.reveal
            (.selected (.controller .this) (.range 1 1)
              (.intersection [
                .wasObjectOfAction 1,
                .union [.subtype .dwarf, .subtype .equipment]]))),
        .returnToHand (.wasObjectOfAction 2)]),
      .putOnLibraryBottomInRandomOrder
        (.intersection [
          .wasObjectOfAction 1,
          .not (.wasObjectOfAction 2)])]))]
#guard parseOracleParts (name := "")
  "This creature has lifelink as long as you control a Dwarf." == none
#guard parseOracleParts (name := "")
  "When this creature enters, look at the top one cards of your library. You may reveal a Dwarf or Equipment card from among them and put it into your hand. Put the rest on the bottom of your library in a random order." ==
  none
#guard parseOracleParts (name := "Smaug, Wicked Worm")
  "Flying\nWhen Smaug enters, create X tapped Treasure tokens, where X is the number of artifacts your opponents control.\nWhenever you cast a spell, if mana from a Treasure was spent to cast it, you draw a card and lose 1 life." ==
  some [
    .ability (.keyword .flying),
    .ability (.triggered (.enter .this)
      (.createTokens (.controller .this)
        (.count (.intersection [
          .permanent, .cardType .artifact,
          .controlled (.opponent (.controller .this))]))
        PredefinedToken.treasureToken
        [.tapped])),
    .ability (.triggered
      (.sequence [
        .spendManaFrom (.subtype .treasure)
          (.triggerId 1 (.castSpell (.intersection [.spell, youControl]))),
        .castSpell (.wasArgumentOfTrigger 1 1)])
      (.sequence [
        .draw (.controller .this) 1,
        .loseLife (.controller .this) 1]))]
#guard parseOracleParts (name := "Gandalf")
  "When Smaug enters, create X tapped Treasure tokens, where X is the number of artifacts your opponents control." ==
  none
#guard parseOracleParts (name := "")
  "When this creature enters, create X Treasure tokens, where X is the number of artifacts your opponents control." ==
  none
#guard parseOracleParts (name := "")
  "Whenever you cast a spell, you draw a card and lose 1 life." ==
  some [.ability
     (.triggered
       (.castSpell
         (.intersection
           [.spell,
            .controlled (.controller .this)]))
       (.sequence
         [.draw (.controller .this) (.nat 1),
          .loseLife
            (.controller .this)
            (.nat 1)]))]
#guard parseOracleParts (name := "Glamdring, Foe-hammer")
  "Instant and sorcery spells you cast cost {X} less to cast, where X is equipped creature's power.\nEquip {2}\n//ADV//\nGleam of Death {3}{U}\nSorcery — Adventure\nMill six cards, then put all instant and sorcery cards from among them into your hand. (Then exile this card. You may cast the artifact later from exile.)" ==
  some [
    .ability (.static (.reduceCostWithX
      (.intersection [
        .spell,
        .union [.cardType .instant, .cardType .sorcery],
        youControl])
      [.mana [.x]]
      (.greatestPower (.hostOf .this)))),
    .ability (.keywordWithCost .equip [.mana [.generic 2]]),
    .alternative [
      .name "Gleam of Death",
      .manaCost [.generic 3, .mono .blue],
      .type .sorcery,
      .subtype .adventure,
      .actions [
        .sequence [
          .actionId 1 (.mill (.controller .this) 6),
          .returnToHand (.intersection [
            .wasObjectOfAction 1,
            .union [.cardType .instant, .cardType .sorcery]])]]]]
#guard parseOracleParts (name := "")
  "Instant and sorcery spells you cast cost {1} less to cast, where X is equipped creature's power." ==
  none
#guard parseOracleParts (name := "")
  "Mill six cards, then put all instant and sorcery card from among them into your hand." ==
  none
#guard parseOracleParts (name := "")
  "Mill four cards, then put all Elf cards from among them into your hand." ==
  some [.actions [.sequence [
    .actionId 1 (.mill (.controller .this) 4),
    .returnToHand
      (.intersection [.wasObjectOfAction 1, .subtype .elf])]]]
#guard parseOracleParts (name := "Cantankerous Keepers")
  "When this creature enters, mill four cards, then put all Elf cards from among them into your hand." ==
  some [.ability (.triggered
    (.enter .this)
    (.sequence [
      .actionId 1 (.mill (.controller .this) 4),
      .returnToHand
        (.intersection [.wasObjectOfAction 1, .subtype .elf])]))]
#guard parseOracleParts (name := "")
  "Mill one cards, then put all Elf cards from among them into your hand." == none
#guard parseOracleParts (name := "")
  "Mill four cards, then put all Elves cards from among them into your hand." == none
#guard parseOracleParts (name := "")
  "Mill four cards, then put all instant cards from among them into your hand." == none
#guard parseOracleParts (name := "Elektra, Daughter of the Hand")
  "When Elektra enters, destroy target creature an opponent controls with power 3 or less." ==
  some [.ability (.triggered
    (.enter .this)
    (.destroy
      (.target 1
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.opponent (.controller .this)),
          .powerAtMost (Value.int 3)]))))]
#guard parseOracleParts (name := "Elektra, Daughter of the Hand")
  "When Gandalf enters, destroy target creature an opponent controls with power 3 or less." ==
  none
#guard parseOracleParts (name := "Settle the Wreckage")
  "Exile all attacking creatures target player controls. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle." ==
  some [.actions [
    .actionId 1
      (.exile
        (.intersection [
          .permanent,
          .cardType .creature,
          .attacking .all,
          .controlled (.target 1 .player)])),
    .optional (.targetReference 1)
      (.searchLibraryThenShuffle
        (.targetReference 1)
        [
          .putOntoBattlefieldInState
            (.selected
              (.targetReference 1)
              (.range (.nat 0) (.count (.wasObjectOfAction 1)))
              (.intersection [
                .inLibrary,
                .cardType .land,
                .supertype .basic]))
            [.tapped]])]]
#guard parseOracleParts (name := "")
  "Exile all attacking creatures. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle." ==
  none
#guard parseOracleParts (name := "Iron Hills Blacksmith")
  "When this creature enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}." ==
  some [.ability (.triggered (.enter .this)
    (.createTokens (.controller .this) 1 [
      .name "Axe",
      .type .artifact,
      .subtype .equipment,
      .colorIndicator [],
      .ability (.static (.addPower (.hostOf .this) (Value.int 1))),
      .ability (.keywordWithCost .equip [.mana [.generic 2]])]))]
#guard parseOracleParts (name := "Iron Hills Blacksmith")
  "When Iron Hills Blacksmith enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}." ==
  parseOracleParts (name := "Iron Hills Blacksmith")
    "When this creature enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}."
#guard parseOracleParts (name := "")
  "When this creature enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +0/+0\" and equip {2}." ==
  none
#guard parseOracleParts (name := "Gandalf, Goblins' Bane")
  "Whenever you cast a noncreature spell, Gandalf gets +1/+1 until end of turn and deals 1 damage to each opponent." ==
  some [.ability (.triggered
    (.castSpell (.intersection [
      .spell, .not (.cardType .creature), .controlled (.controller .this)]))
    (.sequence [
      .continuous [
        .addPower (.source .this) (Value.int 1),
        .addToughness (.source .this) (Value.int 1)]
        .endOfTurn,
      .dealDamage (.source .this) (.opponent (.controller .this)) 1]))]
#guard parseOracleParts (name := "Saruman")
  "Whenever you cast a noncreature spell, Gandalf gets +1/+1 until end of turn and deals 1 damage to each opponent." ==
  none
#guard parseOracleParts (name := "")
  "Look at the top two cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a Wizard." ==
  some [.actions [
    .actionId 1 (.lookAt (.topOfLibrary (.controller .this) 2)),
    .actionId 2 (.exileFaceDown (.wasObjectOfAction 1)),
    .continuous
      [.if
        (.any (.intersection [
          .permanent, .subtype .wizard, .controlled (.controller .this)]))
        [.canPlay
          (.controller .this)
          (.intersection [.inExile, .wasCreatedByAction 2])]]
      .endOfGame]]
#guard parseOracleParts (name := "")
  "Look at the top two cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a Wizard. (Then exile this card. You may cast the creature later from exile.)" ==
  parseOracleParts (name := "")
    "Look at the top two cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a Wizard."
#guard parseOracleParts (name := "")
  "Look at the top one cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a Wizard." ==
  none
#guard parseOracleParts (name := "")
  "Look at the top two cards of your library and exile them face up. For as long as they remain exiled, you may play them if you control a Wizard." ==
  none
#guard OracleParts.parseTargetDesc "up to one other target creature" 1 ==
  some (.targets 1 (.range 0 1) (.intersection [.not .this, .permanent, .cardType .creature]))
#guard parseOracleParts (name := "Azog, Moria's Ruin")
  "When Azog enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card. (To amass Goblins X, that player puts X +1/+1 counters on an Army they control. It's also a Goblin. If they don't control an Army, they create a 0/0 black Goblin Army creature token first.)" ==
  some [.ability (.triggered (.enter .this) (.sequence [
    .defineValueVariable 1
      (.greatestPower
        (.targets 1 (.range 0 1) (.intersection [.not .this, .permanent, .cardType .creature]))),
    .defineSelectorVariable 2 (.controller (.targetReference 1)),
    .destroy (.targetReference 1),
    .keyword (.variable 2) (.amass .goblin (.variable 1)),
    .if (.any (.intersection [.variable 2, .controller .this]))
      [.draw (.controller .this) 1]]))]
#guard parseOracleParts (name := "Azog, Moria's Ruin")
  "When this creature enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card." ==
  parseOracleParts (name := "Azog, Moria's Ruin")
    "When Azog enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card."
#guard parseOracleParts (name := "")
  "When this creature enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's toughness. If you controlled that creature, draw a card." ==
  none
#guard parseOracleParts (name := "Balin, Loremaster")
  "Whenever Balin or another Dwarf you control enters, you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, Balin deals X damage to each opponent." ==
  some [.ability (.triggered
    (.or
      (.enter .this)
      (.enter (.intersection [
        .not .this, .permanent, .cardType .creature, .subtype .dwarf,
        .controlled (.controller .this)])))
    (.sequence [
      .optional (.controller .this)
        (.actionId 1
          (.discard (.controller .this)
            (.count (.intersection [.inHand, .owner (.controller .this)])))),
      .draw (.controller .this) (.count (.wasObjectOfAction 1)),
      .if (.enduringStory (.controller .this))
        [.dealDamage (.source .this) (.opponent (.controller .this))
          (.count (.wasObjectOfAction 1))]]))]
#guard parseOracleParts (name := "Balin, Loremaster")
  "Whenever Balin or another Dwarf you control enters, you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, Thorin deals X damage to each opponent." ==
  none
#guard parseOracleParts (name := "An Unexpected Party")
  "As this enchantment enters, choose a creature type.\nCreatures you control of the chosen type get +2/+2." ==
  some [
    .ability (.static (.replace (.enter .this)
      [.actionId 1 (.chooseCreatureType (.controller .this)), .keepReplacedAction])),
    .ability (.static (.addPower
      (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this),
        .hasCreatureTypeChosenByAction 1])
      (Value.int 2))),
    .ability (.static (.addToughness
      (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this),
        .hasCreatureTypeChosenByAction 1])
      (Value.int 2)))]
#guard parseOracleParts (name := "")
  "As this enchantment enters, choose a creature type." == none
#guard parseOracleParts (name := "")
  "Creatures you control of the chosen type get +2/+2." == none
#guard parseOracleParts (name := "")
  "As this enchantment enters, choose a creature type.\nCreatures you control of the chosen type get +0/+0." ==
  none
#guard parseOracleParts (name := "")
  "Create X 2/2 red Dwarf creature tokens." ==
  some [.actions [
    .createTokens (.controller .this) .x [
      .type .creature, .subtype .dwarf, .colorIndicator [.red], .power 2, .toughness 2]]]
#guard parseOracleParts (name := "")
  "Create X 2/2 red Dwarf creature token." == none
#guard parseOracleParts (name := "")
  "{X}{X}, {T}, Sacrifice this land: Create X Treasure tokens." ==
  some [.ability (.activated
    [.mana [.x, .x], .tapSymbol, .sacrifice .this]
    (.createTokens (.controller .this) .x PredefinedToken.treasureToken))]
#guard parseOracleParts (name := "")
  "{X}{X}, {T}, Sacrifice this land: Create X Treasure token." == none
#guard parseOracleParts (name := "")
  "III, IV — Add {R}." ==
  some [
    .ability (.keywordWithEffect (.chapter 3) [.addMana (.controller .this) [.mono .red]]),
    .ability (.keywordWithEffect (.chapter 4) [.addMana (.controller .this) [.mono .red]])]
#guard parseOracleParts (name := "")
  "II — This Saga gains \"Whenever a land you control enters, draw a card.\"" ==
  some [.ability (.keywordWithEffect (.chapter 2) [
    .continuous
      [.gainAbility .this (.triggered
        (.enter (.intersection [.permanent, .cardType .land, .controlled (.controller .this)]))
        (.draw (.controller .this) 1))]
      .endOfGame])]
#guard parseOracleParts (name := "")
  "II — This Saga gains \"Whenever a land you control enters, draw a card.\" Draw a card." ==
  none
#guard parseOracleParts (name := "")
  "{2}{W}: Two target players each draw a card." ==
  some [.ability (.activated [.mana [.generic 2, .mono .white]]
    (.draw (.targets 1 (.range 2 2) .player) 1))]
#guard parseOracleParts (name := "")
  "{2}{W}: Two target players each draw." == none
#guard parseOracleParts (name := "")
  "When this creature enters, you create a Treasure token." ==
  some [.ability (.triggered (.enter .this)
    (.createTokens (.controller .this) 1 PredefinedToken.treasureToken))]
#guard parseOracleParts (name := "")
  "Create a Treasure token for each Villain you control." ==
  some [.actions [.forEachVariable 1
    (.intersection [.permanent, .subtype .villain, .controlled (.controller .this)])
    [.createTokens (.controller .this) 1 PredefinedToken.treasureToken]]]
#guard parseOracleParts (name := "")
  "Create two Treasure tokens for each Villain you control." == none
#guard parseOracleParts (name := "")
  "Whenever equipped creature deals combat damage to a player, choose a creature type. Create a Treasure token for each creature you control of that type." ==
  some [.ability (.triggered (.combatDamage (.hostOf .this) .player) (.sequence [
    .actionId 1 (.chooseCreatureType (.controller .this)),
    .forEachVariable 2
      (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this),
        .hasCreatureTypeChosenByAction 1])
      [.createTokens (.controller .this) 1 PredefinedToken.treasureToken]]))]
#guard parseOracleParts (name := "")
  "Choose a creature type. Create a Treasure token for each creature you control." == none
#guard parseOracleParts (name := "")
  "Look at the top twenty cards of your library, put any number of land cards from among them onto the battlefield tapped, then shuffle." ==
  some [.actions [
    .actionId 1 (.lookAt (.topOfLibrary (.controller .this) 20)),
    .searchLibraryThenShuffle (.controller .this) [
      .putOntoBattlefieldInState
        (.selected (.controller .this) .any (.intersection [.wasObjectOfAction 1, .cardType .land]))
        [.tapped]]]]
#guard parseOracleParts (name := "")
  "Look at the top twenty cards of your library, put any number of land cards from among them onto the battlefield tapped." ==
  none
#guard parseOracleParts (name := "")
  "At the beginning of combat on your turn, if you've drawn two or more cards this turn, draw a card." ==
  some [.ability (.triggered (.combatStart (.controller .this))
    (.if (.happened (.ordinal 2 .turnStart (.draw (.controller .this) .all)) .turnStart)
      [.draw (.controller .this) 1]))]
#guard parseOracleParts (name := "")
  "At the beginning of combat on your turn, if you've drawn a card this turn, draw a card." == none
#guard parseOracleParts (name := "")
  "At the beginning of lunch, draw a card." == none
#guard parseOracleParts (name := "")
  "The first creature spell you cast each turn costs {1} less to cast and can be cast as though it had flash." ==
  let creatureSpell := Selector.intersection [.spell, .cardType .creature, .controlled (.controller .this)]
  let first := Condition.didNotHappen (.castSpell creatureSpell) .turnStart
  some [
    .ability (.static (.if first [.reduceCost creatureSpell [.mana [.generic 1]]])),
    .ability (.static (.canBeCastAsThoughWithFlashIf creatureSpell first))]
#guard parseOracleParts (name := "")
  "The first creature spell you cast each turn costs {1} less to cast." == none
#guard parseOracleParts (name := "")
  "{T}: Add {C} for each Food you control." ==
  some [.ability (.activated [.tapSymbol]
    (.forEachVariable 1 (.intersection [.permanent, .subtype .food, youControl])
      [.addMana (.controller .this) [.colorless]]))]
#guard parseOracleParts (name := "")
  "Add {R} for each artifact your opponents control." ==
  some [.actions [.forEachVariable 1
    (.intersection [.permanent, .cardType .artifact, .controlled (.opponent (.controller .this))])
    [.addMana (.controller .this) [.colored .red]]]]
#guard parseOracleParts (name := "")
  "{T}: Target creature with power 2 or less can't be blocked this turn." ==
  some [.ability (.activated [.tapSymbol]
    (.continuous [.forbid (.block .all (.target 1
      (.intersection [.permanent, .cardType .creature, .powerAtMost (Value.int 2)])))] .endOfTurn))]
#guard parseOracleParts (name := "")
  "Whenever this creature attacks, it deals damage equal to the number of Dwarves you control to each opponent." ==
  some [.ability (.triggered (.attack .this .all)
    (.dealDamage .this (.opponent (.controller .this))
      (.count (.intersection [.permanent, .subtype .dwarf, youControl]))))]
#guard parseOracleParts (name := "")
  "When this creature enters, draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library." ==
  some [.ability (.triggered (.enter .this) (.sequence [
    .draw (.controller .this) 1,
    .if (.not (.any (.intersection
        [.permanent, .cardType .creature, .supertype .legendary, youControl])))
      [.putOnBottomOfLibrary (.selected (.controller .this) (.range 1 1)
        (.intersection [.inHand, .owner (.controller .this)]))]]))]
#guard parseOracleParts (name := "")
  "When this creature enters, draw a card. Then if you don't control a legendary creature, put two cards from your hand on the bottom of your library." ==
  none
#guard parseOracleParts (name := "")
  "Legendary creatures you control get +2/+1 and have ward {1}." ==
  let legendary := Selector.intersection
    [.permanent, .cardType .creature, youControl, .supertype .legendary]
  some [
    .ability (.static (.addPower legendary (Value.int 2))),
    .ability (.static (.addToughness legendary (Value.int 1))),
    .ability (.static (.gainAbility legendary (.keywordWithCost .ward [.mana [.generic 1]])))]
#guard parseOracleParts (name := "")
  "Nonlegendary creatures you control get +1/+1." ==
  let nonlegendary := Selector.intersection
    [.permanent, .cardType .creature, .not (.supertype .legendary), youControl]
  some [
    .ability (.static (.addPower nonlegendary (Value.int 1))),
    .ability (.static (.addToughness nonlegendary (Value.int 1)))]
#guard parseOracleParts (name := "")
  "{T}: Add {R}{R}. Spend this mana only to cast Dwarf, Equipment, and Saga spells." ==
  some [.ability (.activated [.tapSymbol] (.sequence [
    .actionId 1 (.addMana (.controller .this) [.colored .red, .colored .red]),
    .continuous [.forbid (.spendManaCreatedByAction 1 (.not (.castSpell
      (.intersection [.spell, .union [.subtype .dwarf, .subtype .equipment, .subtype .saga]]))))]
      .endOfTurn]))]
#guard parseOracleParts (name := "")
  "{2}{B}: Return this card from your graveyard to the battlefield tapped. Activate only if you control a legendary creature." ==
  some [.ability (.graveyardActivatedIf
    (.any (.intersection [.permanent, .cardType .creature, .supertype .legendary, youControl]))
    [.mana [.generic 2, .colored .black]]
    (.putOntoBattlefieldInState (.intersection [.inGraveyard, .source .this]) [.tapped]))]
#guard parseOracleParts (name := "")
  "{2}{B}: Return this card from your graveyard to the battlefield tapped." == none
#guard parseOracleParts (name := "")
  "Draw cards equal to the greatest toughness among creatures you control, then put any number of creature cards from your hand onto the battlefield." ==
  some [.actions [
    .draw (.controller .this) (.greatestToughness creaturesYouControl),
    .putOntoBattlefield (.selected (.controller .this) .any
      (.intersection [.inHand, .owner (.controller .this), .cardType .creature]))]]
#guard parseOracleParts (name := "")
  "Whenever another creature you control with power 2 or less enters, you may pay {1}. If you do, draw a card." ==
  some [.ability (.triggered
    (.enter (.intersection [
      .not .this, .permanent, .cardType .creature, youControl, .powerAtMost (Value.int 2)]))
    (.optionalPayFor (.controller .this) [.mana [.generic 1]] [.draw (.controller .this) 1]))]
#guard parseOracleParts (name := "")
  "Whenever another creature you control with power 2 or less enters, you may pay {1}. If you don't, draw a card." ==
  none
#guard parseOracleParts (name := "Minas Tirith Garrison")
  "Minas Tirith Garrison's power is equal to the number of cards in your hand." ==
  some [.ability (.static (.setPower .this
    (.count (.intersection [.inHand, .owner (.controller .this)]))))]
#guard parseOracleParts (name := "Minas Tirith Garrison")
  "Minas Tirith Garrison's power is equal to the number of cards in your graveyard." == none
#guard parseOracleParts (name := "")
  "Whenever this creature attacks, you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way." ==
  some [.ability (.triggered (.attack .this .all) (.sequence [
    .actionId 1 (.tap (.selected (.controller .this) .any
      (.intersection [.permanent, .subtype .human, .not .tapped, youControl]))),
    .draw (.controller .this) (.count (.wasObjectOfAction 1))]))]
#guard parseOracleParts (name := "")
  "Whenever this creature enters or attacks, return target Elf card from your graveyard to your hand. You gain life equal to that card's power." ==
  some [.ability (.triggered (.or (.enter .this) (.attack .this .all)) (.sequence [
    .returnToHand (.target 1 (.intersection [.inGraveyard, .subtype .elf, .owner (.controller .this)])),
    .gainLife (.controller .this) (.greatestPower (.targetReference 1))]))]
#guard parseOracleParts (name := "")
  "{T}, Pay 1 life: Add {B} or {R}." ==
  some [.ability (.activated [.tapSymbol, .life 1]
    (.playerSelectAction (.controller .this) (.range 1 1)
      [.addMana (.controller .this) [.colored .black], .addMana (.controller .this) [.colored .red]]))]
#guard parseOracleParts (name := "Mount Doom")
  "{5}{B}{R}, {T}, Sacrifice Mount Doom and a legendary artifact: Choose up to two creatures, then destroy the rest. Activate only as a sorcery." ==
  some [.ability (.activatedIf (.timeToCastSorcery (.controller .this))
    [.mana [.generic 5, .colored .black, .colored .red], .tapSymbol, .sacrifice .this,
      .sacrificeCount (.intersection [.permanent, .cardType .artifact, .supertype .legendary]) 1]
    (.sequence [
      .defineSelectorVariable 1
        (.selected (.controller .this) (.range 0 2) (.intersection [.permanent, .cardType .creature])),
      .destroy (.intersection [.permanent, .cardType .creature, .not (.variable 1)])]))]
#guard parseOracleParts (name := "Mount Doom")
  "{5}{B}{R}, {T}, Sacrifice Rivendell and a legendary artifact: Choose up to two creatures, then destroy the rest. Activate only as a sorcery." ==
  none
#guard parseOracleParts (name := "")
  "This creature can't block unless you control a Goblin or Orc." ==
  some [.ability (.static (.if
    (.not (.any (.intersection [.permanent, .union [.subtype .goblin, .subtype .orc], youControl])))
    [.forbid (.block .this .any)]))]
#guard parseOracleParts (name := "")
  "Other Orcs and Goblins you control have trample." ==
  some [.ability (.static (.gainAbility
    (.intersection [.not .this, .permanent, .union [.subtype .orc, .subtype .goblin], youControl])
    (.keyword .trample)))]
#guard parseOracleParts (name := "")
  "Whenever this creature attacks, it gets +X/+0 until end of turn, where X is the greatest power among creatures you control." ==
  some [.ability (.triggered (.attack .this .all)
    (.continuous [.addPower (.source .this) (.greatestPower creaturesYouControl)] .endOfTurn))]
#guard parseOracleParts (name := "")
  "When this creature enters, destroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way." ==
  some [.ability (.triggered (.enter .this) (.sequence [
    .actionId 1 (.destroy (.intersection [
      .permanent, .union [.cardType .artifact, .cardType .enchantment],
      .controlled (.opponent (.controller .this))])),
    .gainLife (.controller .this) (.count (.wasObjectOfAction 1))]))]
#guard parseOracleParts (name := "")
  "Choose a creature type. Return all creatures that aren't of the chosen type to their owners' hands." ==
  some [.actions [
    .actionId 1 (.chooseCreatureType (.controller .this)),
    .returnToHand (.intersection [.permanent, .cardType .creature, .not (.hasCreatureTypeChosenByAction 1)])]]
#guard parseOracleParts (name := "")
  "{T}: Add two mana in any combination of {U}, {B}, and/or {R}." ==
  some [.ability (.activated [.tapSymbol] (.addManaInAnyCombination (.controller .this)
    [.colored .blue, .colored .black, .colored .red] 2))]
#guard parseOracleParts (name := "Rivendell")
  "Rivendell enters tapped unless you control a legendary creature." ==
  some [.ability (.everywhereStatic (.if
    (.not (.any (.intersection [.permanent, .cardType .creature, .supertype .legendary, youControl])))
    [.replace (.enter .this) [.putOntoBattlefieldInState .this [.tapped]]]))]
#guard parseOracleParts (name := "")
  "{1}{U}, {T}: Scry 2. Activate only if you control a legendary creature." ==
  some [.ability (.activatedIf
    (.any (.intersection [.permanent, .cardType .creature, .supertype .legendary, youControl]))
    [.mana [.generic 1, .colored .blue], .tapSymbol]
    (.scry (.controller .this) 2))]
#guard parseOracleParts (name := "")
  "Other Elves you control have \"{T}: Add {G} or {U}.\"" ==
  some [.ability (.static (.gainAbility
    (.intersection [.not .this, .permanent, .subtype .elf, youControl])
    (.activated [.tapSymbol] (.playerSelectAction (.controller .this) (.range 1 1)
      [.addMana (.controller .this) [.colored .green], .addMana (.controller .this) [.colored .blue]]))))]
#guard parseOracleParts (name := "") "Other Elves you control have \"Flying.\"" == none
#guard parseOracleParts (name := "")
  "{T}: Add one mana of any color. Spend this mana only to cast a Hero spell or to activate an ability of a Hero source." ==
  some [.ability (.activated [.tapSymbol] (.sequence [
    .actionId 1 (.addManaOfOneColor (.controller .this) ManaSymbol.anyColor 1),
    .continuous [.forbid (.spendManaCreatedByAction 1 (.not (.or
      (.castSpell (.intersection [.spell, .subtype .hero])) (.activateAbility (.subtype .hero)))))]
      .endOfTurn]))]
#guard parseOracleParts (name := "")
  "{T}: Add one mana of any color. Spend this mana only to cast a Hero spell or to activate an ability of a Villain source." ==
  none
#guard parseOracleParts (name := "")
  "{T}: Add one mana of any color. Spend this mana only to cast an artifact spell." ==
  some [.ability (.activated [.tapSymbol] (.sequence [
    .actionId 1 (.addManaOfOneColor (.controller .this) ManaSymbol.anyColor 1),
    .continuous [.forbid (.spendManaCreatedByAction 1
      (.not (.castSpell (.intersection [.spell, .cardType .artifact]))))] .endOfTurn]))]
#guard parseOracleParts (name := "")
  "{T}: Add {U}. This mana can't be spent to cast a nonartifact spell." ==
  some [.ability (.activated [.tapSymbol] (.sequence [
    .actionId 1 (.addMana (.controller .this) [.colored .blue]),
    .continuous [.forbid (.spendManaCreatedByAction 1
      (.castSpell (.intersection [.spell, .not (.cardType .artifact)])))] .endOfTurn]))]
#guard parseOracleParts (name := "")
  "{T}: Add {B} or {R}. Activate only if this land entered this turn or if you control a basic land." ==
  some [.ability (.activatedIf
    (.not (.and (.not (.happened (.enter (.source .this)) .turnStart))
      (.not (.any (.intersection [.permanent, .cardType .land, .supertype .basic, youControl])))))
    [.tapSymbol]
    (.playerSelectAction (.controller .this) (.range 1 1)
      [.addMana (.controller .this) [.colored .black], .addMana (.controller .this) [.colored .red]]))]
#guard parseOracleParts (name := "")
  "{4}, {T}: Look at the top three cards of your library. You may reveal a Hero card from among them and put it into your hand. Put the rest on the bottom of your library in any order." ==
  some [.ability (.activated [.mana [.generic 4], .tapSymbol] (.sequence [
    .actionId 1 (.lookAt (.topOfLibrary (.controller .this) 3)),
    .optional (.controller .this) (.sequence [
      .actionId 2 (.reveal (.selected (.controller .this) (.range 1 1)
        (.intersection [.wasObjectOfAction 1, .subtype .hero]))),
      .returnToHand (.wasObjectOfAction 2)]),
    .putOnBottomOfLibrary (.intersection [.wasObjectOfAction 1, .not (.wasObjectOfAction 2)])]))]
#guard parseOracleParts (name := "")
  "{4}, {T}: Look at the top three cards of your library. You may reveal a Hero card from among them and put it into your hand. Put the rest on the bottom of your library in a random order." ==
  none

#guard parseOracleParts (name := "Quake") "Quake deals 3 damage to each creature." ==
  some [.actions [.dealDamage .this (.intersection [.permanent, .cardType .creature]) 3]]
#guard parseOracleParts (name := "")
  "Destroy target land. Its controller may search their library for a basic land card, put it onto the battlefield tapped, then shuffle." ==
  some [.actions [
    .destroy (.target 1 (.intersection [.permanent, .cardType .land])),
    .optional (.controller (.targetReference 1)) (.searchLibraryThenShuffle (.controller (.targetReference 1)) [
      .putOntoBattlefieldInState (.selected (.controller (.targetReference 1)) (.range 1 1)
        (.intersection [.inLibrary, .cardType .land, .supertype .basic])) [.tapped]])]]
#guard parseOracleParts (name := "")
  "Double target creature's power and toughness until end of turn." ==
  some [.actions [.continuous [
    .addPower (.target 1 (.intersection [.permanent, .cardType .creature])) (.greatestPower (.targetReference 1)),
    .addToughness (.targetReference 1) (.greatestToughness (.targetReference 1))] .endOfTurn]]
#guard parseOracleParts (name := "")
  "Target creature you control fights target creature an opponent controls." ==
  some [.actions [.fight
    (.target 1 (.intersection [.permanent, .cardType .creature, youControl]))
    (.target 2 (.intersection [.permanent, .cardType .creature, .controlled (.opponent (.controller .this))]))]]
#guard parseOracleParts (name := "")
  "Target creature you control deals damage equal to twice its power to target creature an opponent controls." ==
  some [.actions [.dealDamage
    (.target 1 (.intersection [.permanent, .cardType .creature, youControl]))
    (.target 2 (.intersection [.permanent, .cardType .creature, .controlled (.opponent (.controller .this))]))
    (.product (.totalPower (.targetReference 1)) (.int 2))]]
#guard parseOracleParts (name := "")
  "This spell costs {2} less to cast if there are two or more creature cards in your graveyard." ==
  some [.ability (.stackStatic (.if
    (.greaterOrEqual (.count (.intersection [.inGraveyard, .cardType .creature, .owner (.controller .this)])) 2)
    [.reduceCost .this [.mana [.generic 2]]]))]
#guard parseOracleParts (name := "Worlds")
  "Exile all creatures. Each player may put any number of creature cards from their hand onto the battlefield. Then put all cards exiled this way into their owners' hands. Exile Worlds." ==
  some [.actions [
    .actionId 1 (.exile (.intersection [.permanent, .cardType .creature])),
    .forEachVariable 2 .player [.optional (.variable 2) (.putOntoBattlefield
      (.selected (.variable 2) .any (.intersection [.inHand, .owner (.variable 2), .cardType .creature])))],
    .returnToHand (.wasCreatedByAction 1),
    .exile .this]]
#guard parseOracleParts (name := "Worlds")
  "Exile all creatures. Each player may put any number of creature cards from their hand onto the battlefield. Then put all cards exiled this way into their owners' hands. Exile Other Card." ==
  none
#guard parseOracleParts (name := "") "Mill two cards." ==
  some [.actions [.mill (.controller .this) 2]]
#guard parseOracleParts (name := "") "Mill a card." == none
#guard parseOracleParts (name := "HYDRA Troopers")
  "When this creature enters, create a tapped 2/1 black Villain creature token with menace if there are two or more creature cards in your graveyard. Otherwise, mill two cards. (Put the top two cards of your library into your graveyard.)" ==
  some [.ability (.triggered (.enter .this)
    (.ifElse (.greaterOrEqual (.count (.intersection [.inGraveyard, .cardType .creature, .owner (.controller .this)])) 2)
      [.createTokens (.controller .this) 1
        [.type .creature, .subtype .villain, .colorIndicator [.black], .power 2, .toughness 1,
          .ability (.keyword .menace)] [.tapped]]
      [.mill (.controller .this) 2]))]
#guard parseOracleParts (name := "Iron Man, Master of Machines")
  "Whenever Iron Man attacks, if an artifact entered the battlefield under your control this turn, draw a card." ==
  some [.ability (.triggered (.attack .this .all)
    (.if (.happened (.enter (.intersection [.permanent, .cardType .artifact, youControl])) .turnStart)
      [.draw (.controller .this) 1]))]
#guard parseOracleParts (name := "Super Intelligence")
  "At the beginning of the upkeep of enchanted creature's controller, that player draws a card." ==
  some [.ability (.triggered (.upkeep (.controller (.hostOf .this))) (.draw (.controller (.hostOf .this)) 1))]
#guard parseOracleParts (name := "Hulkling, Burgeoning Bruiser")
  "Whenever another creature you control enters, if it has greater power or toughness than Hulkling, put a +1/+1 counter on Hulkling." ==
  some [.ability (.triggered
    (.triggerId 1 (.enter (.intersection [.not .this, .permanent, .cardType .creature, youControl])))
    (.if (.not (.and
        (.not (.greater (.greatestPower (.wasArgumentOfTrigger 1 1)) (.greatestPower (.source .this))))
        (.not (.greater (.greatestToughness (.wasArgumentOfTrigger 1 1)) (.greatestToughness (.source .this))))))
      [.putCounter (.source .this) .plusOnePlusOne 1]))]
#guard parseOracleParts (name := "")
  "Flying, first strike, ward {1}" ==
  some [.ability (.keyword .flying), .ability (.keyword .firstStrike),
    .ability (.keywordWithCost .ward [.mana [.generic 1]])]
#guard parseOracleParts (name := "The Sackville-Bagginses")
  "Whenever you sacrifice a token, target opponent loses 1 life." ==
  some [.ability (.triggered
    (.sacrifice (.intersection [.permanent, .token, youControl]))
    (.loseLife (.target 1 (.opponent (.controller .this))) 1))]
#guard parseOracleParts (name := "The Sackville-Bagginses")
  "Whenever you sacrifice a creature, target opponent loses 1 life." == none
#guard parseOracleParts (name := "The Sackville-Bagginses")
  "Whenever a token you control dies, target opponent loses 1 life." == none
#guard parseOracleParts (name := "The Thing, Ben Grimm")
  "Whenever one or more Heroes you control deal damage to a player, put two +1/+1 counters on The Thing." ==
  some [.ability (.triggered
    (.damageSimultaneously
      (.intersection [
        .permanent, .cardType .creature, .subtype .hero, youControl])
      .player
      [])
    (.putCounter (.source .this) .plusOnePlusOne 2))]
#guard parseOracleParts (name := "The Thing, Ben Grimm")
  "Whenever one or more Heroes you control deal combat damage to a player, put two +1/+1 counters on The Thing." ==
  none
#guard parseOracleParts (name := "Other Card")
  "Whenever one or more Heroes you control deal damage to a player, put two +1/+1 counters on The Thing." ==
  none

end Mtg.Engine
