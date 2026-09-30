import Mtg.Engine.OracleRulings.Data

/-!
# Unique Oracle rulings

Judge-issued Oracle rulings (Gatherer / Scryfall `wotc` comments, plus
MSH release notes) for unique cards in `The Hobbit` (HOB),
`The Hobbit Eternal` (HOC), and
`Magic: The Gathering | Marvel Super Heroes` (MSH). These are
not the rules text printed on the cards and are not Comprehensive
Rules citations. They are clarifications published by Wizards for
judges and players. Shared comments that appear on many cards
(Adventure, amass, landfall, Power-up, Teamwork, and so on) are
kept once, even when those cards come from different sets.

The comments are `OracleRulings.Data`, which does not import the engine
tests, so that module builds alongside the catalogs. Behavior checks are
`OracleRulings.RulingTests` and `OracleRulings.MshRulingTests`. Those
modules are library roots rather than imports of this file, so they
compile in parallel with the demo instead of blocking it.

Collected 728 unique comments from
1480 ruling instances on
500 cards
(193 HOB, 117 HOC, 190 MSH).
-/
